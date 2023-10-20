(** an OCaml plugin to perform reification and apply the lemmas implementing enhanced coinduction.
    see end-user tactics in [tactics.v]
 *)  

open Constr
open EConstr
open Proofview

(* raise an error in Coq *)
let error s = Printf.kprintf (fun s -> CErrors.user_err (Pp.str s)) ("[coinduction] "^^s)

(* access to Coq constants *)
let get_const s = 
  lazy (EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref s)))

(* make an application using a lazy value *)
let force_app f = fun x -> mkApp (Lazy.force f,x)

(* typecheck a term and propagate universe constraints *)
let typecheck t =
  Goal.enter (fun goal ->
      let env = Tacmach.pf_env goal in
      let sigma = Tacmach.project goal in
      let sigma, _ = Typing.solve_evars env sigma t in
      Unsafe.tclEVARS sigma)

(* corresponding application tactics *)
let typecheck_and_apply t = tclTHEN (typecheck t) (Tactics.apply t)
let typecheck_and_eapply t = tclTHEN (typecheck t) (Tactics.eapply t)

(* creating OCaml functions from Coq ones *)
let get_fun_1 s = let v = get_const s in fun x -> force_app v [|x|]
let get_fun_2 s = let v = get_const s in fun x y -> force_app v [|x;y|]
(* let get_fun_3 s = let v = get_const s in fun x y z -> force_app v [|x;y;z|] *)
let get_fun_4 s = let v = get_const s in fun x y z t -> force_app v [|x;y;z;t|]
let get_fun_5 s = let v = get_const s in fun x y z t u -> force_app v [|x;y;z;t;u|]

(* Coq constants *)
module Coq = struct
  let and_    = get_const "core.and.type"
  let pair    = get_fun_4 "core.prod.intro"
end

(* Coinduction constants *)
module Cnd = struct
  let body_       = get_const "coinduction.body"
  let body        = get_fun_4 "coinduction.body"            
  let elem_       = get_const "coinduction.elem"
  let elem        = get_fun_4 "coinduction.elem"
  let chain       = get_const "coinduction.Chain"
  let gfp         = get_const "coinduction.gfp"
  let symmetrical = get_const "coinduction.Symmetrical"
  let ar_prp      = get_const "coinduction.PRP"
  let ar_abs      = get_fun_2 "coinduction.ABS"
  let tuple       = get_fun_1 "coinduction.tuple"
  let hol         = get_const "coinduction.hol"
  let abs         = get_fun_2 "coinduction.abs"
  let cnj         = get_fun_2 "coinduction.cnj"
  let fT          = get_fun_2 "coinduction.fT"
  let pT_         = get_const "coinduction.pT"
  let pT          = get_fun_4 "coinduction.pT"
  let tnil        = get_fun_1 "coinduction.tnil"
  let tcons       = get_fun_4 "coinduction.tcons"
  let ptower      = get_fun_5 "coinduction.ptower"
  let by_symmetry = get_fun_4 "coinduction.by_symmetry"
end 

(* applying one of the [reification.ptower/by_symmetry] lemmas 
   and changing the obtained goal back into a user-friendly looking goal.
   [rname] is the name of the chain element under focus (i.e., the current bisimulation candidate)
   Depending on the lemma we want to apply
   [mode] is either
   - `PTower(n)
   - `By_symmetry
   In first case, [n] is the number of hypotheses to exploit (represented as a Coq constr of type [nat]).
 *)
  
let apply rname mode goal =
   (* first we determine the following values: 
      [s] is the type of elements this function operates on
      [l] is the corresponding complete lattice
      [b] is the monotone function of the coinductive game
      [rel] is a relation of type [s]
      [a] is the arity corresponding to [s]  
    *)
  let env = Tacmach.pf_env goal in
  let sigma = Tacmach.project goal in
  let debug c = ignore (Feedback.msg_warning (Printer.pr_leconstr_env env sigma c)) in
  let convertible = Reductionops.is_conv env sigma in
  let _ = debug in
  let rconstr = mkVar rname in
  let _,rtype = Typing.type_of env sigma rconstr in  
  let (s,l,b) = match kind sigma rtype with
    | App(c,[|s;l;b|]) when c=Lazy.force Cnd.chain -> (s,l,b)
    | _ -> error "expecting a chain element as candidate"
  in
  let rel = Cnd.elem s l b rconstr in
  let a =
    (* when [s] is [A -> B -> Prop], returns [ABS A (ABS B PRP)] *)
    let rec get_arity s = 
      match kind sigma (Reductionops.whd_all env sigma s) with
      | Sort _ -> Lazy.force Cnd.ar_prp
      | Prod(i,a,q) -> Cnd.ar_abs a (mkLambda(i,a,get_arity q))
      | _ -> error "coinductive object must be a n-ary relation"
    in
    get_arity s
  in
  let tuple xs = mkApp (Cnd.tuple a, Array.of_list xs) in
  let swap v xs =
    if v then Array.of_list xs
    else match xs with [x;y] -> [|y;x|]
         | _ -> failwith "by_symmetry: not a binary relation (please report)"
  in
  
  (* key function: parsing/reifying a type [e] of the shape

     [forall x y, P x y -> ?REL u v /\ forall z, ?REL p q]

     where x,y may appear in P, u, v, p, q and z may appear in p q
     and where REL is constrained by the current mode:
     - should be [elem R] for the considered chain element [R] with `Accumulate
     - should be [b (elem R)] for the considered chain element [R] with `By_symmetry
     
     such a type [e] is interpreted as a bisimulation candidate

     returns a tuple [(r,c,x,q)] where
     - [c] has type [reification.T] and is the skeleton of the bisimulation candidate
     - [x] has type [reification.fT a c] and are the elements related by the bisimulation candidate
     - [q] is a function making it possible to reconstruct a nice type for the goal resulting from the application of the considered lemma.
     
     the key invariant is that [e] should be convertible to [pT a c r x]

     in the above example,
     - [c] is [abs (fun x => abs (fun y => abs (fun _: P x y => cnj hol (abs (fun z => hol)))))]
     - [x] is [fun x y H => ((u,(v,tt)), fun z => (p,(q,tt)))]

     the OCaml type of [g] is a bit complicated: [bool -> int -> (int -> constr) -> constr]
     intuitively, [g true i REL'] should be [e] where [REL] has beend replaced by [REL']
     the integers are there to deal with de Bruijn indices:
     - in the `PTower case, [REL'] will constructed from the context so that integers will just be ignored 
     - in the `By_symmetry case, [REL'] involves a [mkRel] whose index depends on the depth at wich it gets replaced; [i] is used to record the current depth 
     the Boolean is only used for the `By_symmetry mode: setting it to false makes it possible to reverse all pairs in the candidate
   *)
  let rec parse e =
    match kind sigma e with
    (* both universal quantification and implication *)
    | Prod(i,w,q) ->
       let (c,x,g) = parse q in
       (Cnd.abs w (mkLambda(i,w,c)),
        mkLambda(i,w,x),
        (fun v l r -> mkProd(i,w,g v (l+1) r)))
    (* conjunction *)
    | App(c,[|p1;p2|]) when c=Lazy.force Coq.and_ ->
       let (c1,x1,g1) = parse p1 in
       let (c2,x2,g2) = parse p2 in
       (Cnd.cnj c1 c2,
        Coq.pair (Cnd.fT a c1) (Cnd.fT a c2) x1 x2,
        (fun v l r -> mkApp(c,[|g1 v l r;g2 v l r|])))
    (* elem s l b r ... *)
    | App(c,slbr_) when mode <>`By_symmetry && c=Lazy.force Cnd.elem_ ->
       (match Array.to_list slbr_ with
        | _::_::_::r'::xs ->
           if not (convertible r' rconstr) then
             error "only one candidate is allowed";
           (Lazy.force Cnd.hol,tuple xs,
            (fun v l r -> mkApp(r l,swap v xs)))
        | _ -> assert false)
    (* body s l b r x y *)      
    | App(c,slbrxy) when mode =`By_symmetry && c=Lazy.force Cnd.body_ ->
       (match slbrxy with
          [|_;_;b';r';x;y|] ->
           if not (convertible r' rel &&convertible b' b) then
             error "only one candidate is allowed";
           (Lazy.force Cnd.hol,tuple [x;y],
            (fun v l r -> mkApp(r l,swap v [x;y])))
          | _ -> error "binary relation expected for reasonning by symmetry")
    (* gfp b (should be dealt with beforehand) *)
    | App(c,_) when c = Lazy.force Cnd.gfp -> error "only one coinductive predicate is allowed"       
    (* other cases are not handled *)
    | _ -> error "unsupported subterm"
  in

  (* extension of the above function for `Accumulate(n):
     parsing/reifying a type [e] of the shape

     P1 -> ... -> Pn -> P
     
     where P and the Pi's are all of the shape described above for [parse]

     returns a tuple [(cs,c,x,g)] where
     - [cs] has type [reification.Ts a] and contains the reified form of P1...Pn
     - [c,x] is the reified form of P, as above in [parse]
     - [g] is a nice type for the goal resulting from the application of the accumulation lemma, i.e.,
       P1 -> ... -> Pn -> P -> P'
       where P' is obtained from P by replacing [r] with [b r]

     the key invariant is that the starting type [e] 
     should be convertible to [pTs a cs r (pT a c r x)]
   *)
  let rec parse_acc n e =
    match kind sigma n with
    | App(_,[|n|]) ->
       begin                    (* S n *)
         match kind sigma e with
         | Prod(i,l,q) ->
            let (d,u,l') = parse l in
            let (cs,c,x,g) = parse_acc n q in
            (Cnd.tcons a d u cs, c, x, mkProd(i,l' true 0 (fun _ -> rel),g))
         | _ -> failwith "anomaly, mismatch in hypotheses number (please report)"
       end
    | _ ->                      (* 0 *)
       let (c,x,e') = parse e in
       (Cnd.tnil a, c, x,
        mkArrowR
          (e' true 0 (fun _ -> rel))
          (e' true 0 (fun _ -> Cnd.body s l b rel)))
  in

  (* main entry point *)
  match mode with
  | `PTower i ->
     let (cs,c,x,g) = parse_acc i (Tacmach.pf_concl goal) in
     (* here we first revert R and re-introduce it afterwards in order to keep the same name for the candidate.
        we do so in OCaml rather than in Ltac: this makes it possible to avoid the mess with de Bruijn indices *)
     (* debug (Cnd.ptower a b cs c x); *)
     (* debug g; *)
     tclTHEN (Tactics.revert [rname])
       (tclTHEN (typecheck_and_apply (Cnd.ptower a b cs c x))
          (tclTHEN (Tactics.introduction rname)
             (Tactics.convert_concl ~cast:false ~check:true g DEFAULTcast)
       ))
     
  | `By_symmetry ->
     let (c,x,g) = parse (Tacmach.pf_concl goal) in
     (* several catches here...

        1. We would like to do just
        [Tactics.apply (by_symmetry a c x b)]
        unfortunately, this does not seem to trigger typeclass resolution for instantiating the next two arguments of [by_symmetry] (the function s, and a proof of [Sym_from converse b s])
        Thus we use [eapply] instead, and we perform an explicit call to typeclass resolution for the first generated subgoal. 

        2. The unification problem seems to be more difficult here, and [eapply] fails unless we convert the goal first into its reified form.
        Using [refine (by_symmetry a c x b _ _ _ _)] works in Ltac, but it's painful to provide a term with holes in OCaml - at least I don't know how to do it nicely.
        Whence the first two steps.

        3. after eapplying [by_symmetry], we get three subgoals and we want to
        - run typeclass resolution on the first one
        - do a change with nice types on the second and third ones 
        I don't know how to get access to those three goals separately (e.g., the tclTHENLAST tacticial has a different type than the tclTHEN I'm using here...), so that I take a look at the resulting goals to recognise who is who.
      *)
     let p = Cnd.pT a c (Cnd.body s l b rel) x in
     let a' =
       match kind sigma a with
       | App(_,[|a';_|]) -> a'
       | _ -> assert false
     in
     (* debug (Cnd.by_symmetry a' c x b); *)
     (* debug p; *)
     tclTHEN (Tactics.convert_concl ~cast:false ~check:true p DEFAULTcast)
       (tclTHEN (typecheck_and_eapply (Cnd.by_symmetry a' c x b))
       (Goal.enter (fun goal ->
            let sigma = Tacmach.project goal in
            match kind sigma (Tacmach.pf_concl goal) with
            (* first subgoal (typeclass resolution)*)
            | App(c,_) when c=Lazy.force Cnd.symmetrical ->
               Class_tactics.typeclasses_eauto [Class_tactics.typeclasses_db] ~depth:(Some 5)
            (* third subgoal (main goal) is of the shape [pT a r' c x] *)
            | App(c,[|_;_;r';_|]) when c=Lazy.force Cnd.pT_ ->
               (* here we need to look at the goal anyways, in order to discover the relation [r'] built from the function found by typeclass resolution, and use it to give a nice type *)
               let p' = (g true 0 (fun _ -> r'))  in
               Tactics.convert_concl ~cast:false ~check:true p' DEFAULTcast
            (* second subgoal (symmetry argument) *)               
            | _ -> 
               let p' =
                 mkProd (Context.nameR rname (* (Names.Id.of_string "R") *), s,
                         mkArrowR (g true 1 mkRel) (g false 2 mkRel))
               in
               (* debug p'; *)
               Tactics.convert_concl ~cast:false ~check:true p' DEFAULTcast
       )))
