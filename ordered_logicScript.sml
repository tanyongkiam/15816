open HolKernel relationTheory BasicProvers listTheory arithmeticTheory

val _ = new_theory"ordered_logic";

val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0;

val _ = temp_tight_equality();

(* Representation of ordered logic terms *)
val _ = Datatype`
  term = Var num (* For simplicity, Var names are numbers*)
       | Over term term (* x / y *)
       | Under term term (* y \ x (y is second arg)  *)
       | Fuse term term (* x . y *)
       | Twist term term (* x o y *)
       | Ext term term (* x & y *)
       | Int term term (* x + y *)
       | One (* 1 *)`

(* A sequent is a pair of (antecedent list,succedent)
  Each *-dent is a term of ordered logic
*)

val _ = type_abbrev ("sequent", ``:term list # term``)

(* Identifiers for the connectives in each rule *)
val _ = Datatype`
  ruleId = Id | Ov | Un | Fu | Tw | Ex | In | On | Cut `

(* The rules have four additional arguments
  ruleIds label the rule and the number gives a size induction principle
  The last two args turns on/off cuts and restricts ids
*)

val (rules_def,rules_ind,rules_cases) = Hol_reln`
  (* Cut is only enabled when the cut flag is set
  ct |- x  ctL x ctR |- z
  ---- CUT
  ctL ct ctR |- z *)
  (rules l n cut id (ct,x) ∧ rules l' m cut id (ctL ++ [x] ++ ctR,z) ∧ cut ⇒
  rules (INL Cut) (n+m+1) cut id (ctL++ct++ctR,z)) ∧

  (* When the Id flag is set, identity is enabled for all terms otherwise, it only applies at variables
  ----(Id)
  x |- x
  *)
  ((¬id ⇒ ∃n. x = Var n) ⇒
  rules (INL Id) 0n cut id (([x],x):sequent)) ∧

  (*
  ct y |- x
  --- (/R)
  ct |- x/y
  *)
  (∀n (ct:term list) x y.
  rules l n cut id (ct++[y],x) ⇒
  rules (INR Ov) (n+1) cut id (ct,Over x y)) ∧
  (*
  ctL x ctR |-z  ct |- y
  --- (/L)
  ctL x/y ct ctR |- z
  *)
  (∀n m (ct:term list) y.
  rules l m cut id (ct,y) ∧ rules l' n cut id (ctL++[x]++ctR,z) ⇒
  rules (INL Ov) (n+m+1) cut id (ctL++[(Over x y)]++ct++ctR,z)) ∧

  (*
  y ct |- x
  --- (\R)
  ct |- y\x
  *)
  (∀n (ct:term list) x y.
  rules l n cut id (y::ct,x) ⇒
  rules (INR Un) (n+1) cut id (ct,Under x y)) ∧
  (*
  ctL x ctR |-z  ct |- y
  --- (\L)
  ctL ct y/x ctR |- z
  *)
  (∀n m (ct:term list) y.
  rules l m cut id (ct,y) ∧ rules l' n cut id (ctL++[x]++ctR,z) ⇒
  rules (INL Un) (n+m+1) cut id (ctL++ct++[(Under x y)]++ctR,z)) ∧

  (*
  ctL |- x ctR |- y
  --- (.R)
  ctL ctR |- x.y
  *)
  (∀n m (ctL:term list) ctR x y.
  rules l n cut id (ctL,x) ∧ rules l' m cut id (ctR,y) ⇒
  rules (INR Fu) (n+m+1) cut id (ctL++ctR,Fuse x y)) ∧
  (*
  ctL x y ctR |-z
  --- (.L)
  ctL x.y ctR |- z
  *)
  (∀n (ctL:term list) ctR x y.
  rules l n cut id (ctL++[x]++[y]++ctR,z) ⇒
  rules (INL Fu) (n+1) cut id (ctL++[Fuse x y]++ctR,z)) ∧

  (*
  ctL |- x ctR |- y
  --- (oR)
  ctR ctL |- x o y
  *)
  (∀n m (ctL:term list) ctR x y.
  rules l n cut id (ctL,x) ∧ rules l' m cut id (ctR,y) ⇒
  rules (INR Tw) (n+m+1) cut id (ctR++ctL,Twist x y)) ∧
  (*
  ctL x y ctR |-z
  --- (oL)
  ctL y o x ctR |- z
  *)
  (∀n (ctL:term list) ctR x y.
  rules l n cut id (ctL++[y]++[x]++ctR,z) ⇒
  rules (INL Tw) (n+1) cut id (ctL++[Twist x y]++ctR,z)) ∧

  (*
  ct |- x ct |- y
  --- (&R)
  ct |- x&y
  *)
  (∀n m (ct:term list) x y.
  rules l n cut id (ct,x) ∧ rules l' m cut id (ct,y) ⇒
  rules (INR Ex) (n+m+1) cut id (ct,Ext x y)) ∧
  (*
  ctL x ctR |-z
  --- (&L1)
  ctL x&y ctR |- z
  *)
  (∀n (ctL:term list) ctR x y.
  rules l n cut id (ctL++[x]++ctR,z) ⇒
  rules (INL Ex) (n+1) cut id (ctL++[Ext x y]++ctR,z)) ∧
  (*
  ctL y ctR |-z
  --- (&L2)
  ctL x&y ctR |- z
  *)
  (∀n (ctL:term list) ctR x y.
  rules l n cut id (ctL++[y]++ctR,z) ⇒
  rules (INL Ex) (n+1) cut id (ctL++[Ext x y]++ctR,z)) ∧

  (*
  ct |- x
  --- (+R1)
  ct |- x+y
  *)
  (∀n (ct:term list) x y.
  rules l n cut id (ct,x) ⇒
  rules (INR In) (n+1) cut id (ct,Int x y)) ∧
  (*
  ct |- y
  --- (+R2)
  ct |- x+y
  *)
  (∀m (ct:term list) x y.
  rules l' m cut id (ct,y) ⇒
  rules (INR In) (m+1) cut id (ct,Int x y)) ∧
  (*
  ctL x ctR |-z ctL y ctR |-z
  --- (+L)
  ctL x+y ctR |- z
  *)
  (∀n m (ctL:term list) ctR x y.
  rules l n cut id (ctL++[x]++ctR,z) ∧ rules l' m cut id (ctL++[y]++ctR,z) ⇒
  rules (INL In) (n+m+1) cut id (ctL++[Int x y]++ctR,z)) ∧

  (*
  ---- (1R)
  |- 1
  *)
  (rules (INR On) n cut id ([],One)) ∧
  (*
  ctL ctR |- z
  ---- (1L)
  ctL 1 ctR |- z
  *)
  (rules l n cut id (ctL++ctR,z) ⇒
  rules (INL On) (n+1) cut id (ctL++[One]++ctR,z))`

(* Cut admissibility
  ...
  ---           ---
  ct |- x       ctL x ctR |- z
  ⇒
  ---
  ctL ct ctR |- z
*)

val list_simps = prove(``
  ((A ++ [B] ++ C = [D]) ⇔ A = [] ∧ C = [] ∧ B = D) ∧
  w ++ [x;y] ++ z = w ++ [x] ++([y]++z)``,
  Cases_on`A`>>Cases_on`C`>>fs[])

fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th));

val rules_case1 = (fst(EQ_IMP_RULE (SPEC_ALL rules_cases)))

(* specs the first assum and solves using rules_def -- append assoc where necessary *)
fun smash q b =
  (first_x_assum(qspec_then q mp_tac)>>fs[]>>
  disch_then drule>>fs[]>>
  (if b then FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] else ALL_TAC)>>
  disch_then drule>>rw[]>>
  metis_tac[APPEND_ASSOC,rules_def])

val admissibility = prove(``
  ∀n m x ct ctL ctR z l l' b.
  rules l n F b (ct,x) ∧ rules l' m F b (ctL ++ [x] ++ ctR,z) ⇒
  ∃sz l''. rules l'' sz F b (ctL++ct++ctR,z)``,
  (* Lexicographical induction on size of formula, followed by both derivation trees *)
  completeInduct_on`term_size x`>>
  ntac 2 strip_tac>>
  completeInduct_on`n`>>
  completeInduct_on`m`>>
  fs[PULL_FORALL,GSYM AND_IMP_INTRO]>>
  ntac 6 strip_tac>>
  (* Identity on left *)
  Cases_on`l = INL Id`>>fs[]
  >-
    (simp[Once rules_cases]>>
    metis_tac[rules_cases])
  >>
  (* Identity on right *)
  Cases_on`l' = INL Id`>>fs[]
  >-
    (ntac 2 strip_tac>>simp[Once rules_cases]>>
    rw[list_simps]>>fs[]>>
    metis_tac[rules_cases])
  >>
  (* Commutative L rules on left *)
  Cases_on`l`
  >-
    (Cases_on`x'`>>simp[Once rules_cases]>>rw[]>>
    last_assum(qspec_then`n'` mp_tac)>>fs[]>> rpt (disch_then drule)>>
    TRY(last_assum(qspec_then`m'` mp_tac)>>fs[]>> rpt (disch_then drule))>>
    rw[]>>
    metis_tac[rules_def,APPEND_ASSOC])
  >>
  (* Commutative R rules on right *)
  reverse(Cases_on`l'`)
  >-
    (ntac 2 strip_tac>>
    Cases_on`y'`>>
    strip_tac>>drule rules_case1>>rw[]>>
    fs[APPEND_EQ_APPEND_MID]>>rfs[]
    >- smash `n'` true
    >- metis_tac[rules_def,APPEND_ASSOC,EVAL``[A]++B=A::B``,DECIDE``A < A + (B+1) ∧ B < A+(B+1) ∧ n < n+1``]
    (* These could probably be done directly with metis, but smash makes it slightly faster *)
    >- smash `n'` true
    >- smash `m'` false
    >- smash `m'` false
    >- smash `n'` false
    >- metis_tac[rules_def,APPEND_ASSOC,EVAL``[A]++B=A::B``,DECIDE``A < A + (B+1) ∧ B < A+(B+1) ∧ n < n+1``]
    >- metis_tac[rules_def,APPEND_ASSOC,EVAL``[A]++B=A::B``,DECIDE``A < A + (B+1) ∧ B < A+(B+1) ∧ n < n+1``]
    >- metis_tac[rules_def,APPEND_ASSOC,EVAL``[A]++B=A::B``,DECIDE``A < A + (B+1) ∧ B < A+(B+1) ∧ n < n+1``])
  >>
  ntac 3 strip_tac>>
  Cases_on`x'`>>
  drule rules_case1>>rw[]
  >-
    (*Ov L*)
    (fs[APPEND_EQ_APPEND_MID,list_simps]>>rfs[]
    >- smash `m'` false
    >- (* Principal match *)
      (rw[]>>
      qpat_x_assum`rules _ _ _ _ (ct,_)` assume_tac>>
      drule rules_case1>>rw[]>>
      fs[fetch "-" "term_size_def"]>>
      first_assum(qspec_then`x'` mp_tac)>>fs[]>>
      disch_then drule>>
      disch_then drule>>rw[]>>
      first_x_assum(qspec_then`y'` mp_tac)>>fs[]>>
      disch_then drule>>
      metis_tac[])
    >- smash `n'` true
    >- smash `n'` false)
  >-
    (*Un L*)
    (fs[APPEND_EQ_APPEND_MID,list_simps]>>rfs[]
    >- smash `n'` true
    >- smash `m'` false
    >- (* Principal match *)
      (rw[]>>
      qpat_x_assum`rules _ _ _ _ (ct,_)` assume_tac>>
      drule rules_case1>>rw[]>>
      fs[fetch "-" "term_size_def"]>>
      first_assum(qspec_then`x'` mp_tac)>>fs[]>>
      disch_then drule>>
      disch_then drule>>rw[]>>
      first_x_assum(qspec_then`y'` mp_tac)>>fs[]>>
      disch_then drule>>
      metis_tac[APPEND_ASSOC,EVAL``[A]++B=A::B``])
    >- smash`n'` false)
  >-
    (* Fu L *)
    (fs[APPEND_EQ_APPEND_MID,list_simps]>>rfs[]
    >- smash `n'` true
    >- (* Principal match *)
      (rw[]>>
      qpat_x_assum`rules _  _ _ _ (ct,_)` assume_tac>>
      drule rules_case1>>rw[]>>
      fs[fetch "-" "term_size_def"]>>
      first_assum(qspec_then`x'` mp_tac)>>fs[]>>
      disch_then drule>>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]>>
      disch_then drule>>
      first_x_assum(qspec_then`y'` mp_tac)>>fs[]>>
      disch_then drule>>
      metis_tac[APPEND_ASSOC,EVAL``[A]++B=A::B``])
    >- smash `n'` false)
  >-
    (* Tw L *)
    (fs[APPEND_EQ_APPEND_MID,list_simps]>>rfs[]
    >- smash `n'` true
    >- (* Principal match *)
      (rw[]>>
      qpat_x_assum`rules _  _ _ _ (ct,_)` assume_tac>>
      drule rules_case1>>rw[]>>
      fs[fetch "-" "term_size_def"]>>
      first_assum(qspec_then`y'` mp_tac)>>fs[]>>
      disch_then drule>>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]>>
      disch_then drule>>
      first_assum(qspec_then`x'` mp_tac)>>fs[]>>
      disch_then drule>>
      metis_tac[APPEND_ASSOC,EVAL``[A]++B=A::B``])
    >- smash `n'` false)
  >-
    (* Ex L 1 *)
    (fs[APPEND_EQ_APPEND_MID,list_simps]>>rfs[]
    >- smash `n'` true
    >- (* Principal match *)
      (rw[]>>
      qpat_x_assum`rules _  _ _ _ (ct,_)` assume_tac>>
      drule rules_case1>>rw[]>>
      fs[fetch "-" "term_size_def"]>>
      first_assum(qspec_then`x'` mp_tac)>>fs[]>>
      disch_then drule>>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]>>
      disch_then drule>>
      first_x_assum(qspec_then`y'` mp_tac)>>fs[]>>
      disch_then drule>>
      metis_tac[APPEND_ASSOC,EVAL``[A]++B=A::B``])
    >- smash`n'` false)
  >- (* Ex L 2*)
    (fs[APPEND_EQ_APPEND_MID,list_simps]>>rfs[]
    >- smash `n'` true
    >- (* Principal match *)
      (rw[]>>
      qpat_x_assum`rules _ _ _ _ (ct,_)` assume_tac>>
      drule rules_case1>>rw[]>>
      fs[fetch "-" "term_size_def"]>>
      first_assum(qspec_then`y'` mp_tac)>>fs[]>>
      disch_then drule>>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]>>
      disch_then drule>>
      first_x_assum(qspec_then`x'` mp_tac)>>fs[]>>
      disch_then drule>>
      metis_tac[APPEND_ASSOC,EVAL``[A]++B=A::B``])
    >- smash `n'` false)
  >- (* In L*)
    (fs[APPEND_EQ_APPEND_MID,list_simps]>>rfs[]
    >-
      (first_assum(qspec_then`n'` mp_tac)>>fs[]>>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rpt (disch_then drule)>>
      first_assum(qspec_then`m'` mp_tac)>>fs[]>>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rpt (disch_then drule)>>
      rw[]>>
      metis_tac[rules_def,APPEND_ASSOC])
    >- (* Principal match *)
      (rw[]>>
      qpat_x_assum`rules _ _ _ _ (ct,_)` assume_tac>>
      drule rules_case1>>rw[]>>
      fs[fetch "-" "term_size_def"]
      >-
        (first_assum(qspec_then`x'` mp_tac)>>fs[]>>
        disch_then drule>>
        FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]>>
        disch_then drule>>
        first_x_assum(qspec_then`y'` mp_tac)>>fs[]>>
        disch_then drule>>
        metis_tac[APPEND_ASSOC,EVAL``[A]++B=A::B``])
      >-
        (first_assum(qspec_then`y'` mp_tac)>>fs[]>>
        disch_then drule>>
        FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]>>
        disch_then drule>>
        first_x_assum(qspec_then`x'` mp_tac)>>fs[]>>
        disch_then drule>>
        metis_tac[APPEND_ASSOC,EVAL``[A]++B=A::B``]))
    >-
      (first_assum(qspec_then`n'` mp_tac)>>fs[]>>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rpt (disch_then drule)>>
      first_assum(qspec_then`m'` mp_tac)>>fs[]>>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rpt (disch_then drule)>>
      rw[]>>
      metis_tac[rules_def,APPEND_ASSOC]))
  >- (* On L *)
    (fs[APPEND_EQ_APPEND_MID,list_simps]>>rfs[]
    >- smash `n'` true
    >- (* Principal match *)
      (rw[]>>
      qpat_x_assum`rules _ _ _ _ (ct,_)` assume_tac>>
      drule rules_case1>>rw[]>>
      metis_tac[])
    >- smash `n'` false));

val cut_elimination = prove(``
  ∀l n cut id seq.
  rules l n cut id seq ⇒
  cut = T ⇒
  ∃l' n'. rules l' n' F id seq``,
  ho_match_mp_tac (fetch "-" "rules_ind")>>fs[]>>rw[]
  >-
    metis_tac[admissibility]
  >>
    metis_tac[rules_def])

val id_elimination = prove(``
  ∀l n cut id seq.
  rules l n cut id seq ⇒
  id = F ⇒
  ∃l' n'. rules l' n' cut T seq``,
  ho_match_mp_tac (fetch "-" "rules_ind")>>fs[]>>rw[]>>
  metis_tac[rules_def])

val consistency = prove(``
 ∀l n cut id x.
  ¬(rules l n cut id ([],Var x))``,
  CCONTR_TAC>>fs[]>>
  imp_res_tac cut_elimination>>
  pop_assum mp_tac>>
  fs[Once rules_cases])

val _ = export_theory();
