theory a1
imports Main
begin


section "Q1: \<lambda>-Calculus"

(* TODO: provide your answers here or in an separate PDF file *)




section "Q2: Types"

(* TODO: provide your answers here or in an separate PDF file *)




section "Q3: Propositional Logic"

(*
You must use only these proof methods:
  - rule, erule, assumption, cases, frule, drule,
    rule_tac, erule_tac, frule_tac, drule_tac, rename_tac, case_tac

You must use only these proof rules:
   - impI, impE, conjI, conjE, disjI1, disjI2, disjE, notI, notE
     iffI, iffE, iffD1, iffD2, ccontr, classical, FalseE,
     TrueI, conjunct1, conjunct2, mp
*)


lemma prop_a: "X \<longrightarrow> \<not>\<not>X"
  (* TODO *)
  oops


lemma prop_b: "(X \<longrightarrow> Y \<longrightarrow> \<not> X) \<longrightarrow> X \<longrightarrow> \<not> Y"
  (* TODO *)
  oops


lemma prop_c: "\<not>\<not> A \<longrightarrow> A"
  (* TODO *)
  oops


lemma prop_d: "\<not>(A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  (* TODO *)
  oops


lemma prop_e: "\<not> (A \<longrightarrow> B) \<longrightarrow> A"
  (* TODO *)
  oops


lemma prop_f: "\<not>A\<and>\<not>B \<longleftrightarrow> \<not>(A\<or>B)"
  (* TODO *)
  oops


lemma prop_g: "(A \<longrightarrow> B) \<longrightarrow> (((B \<longrightarrow> C) \<longrightarrow> A) \<longrightarrow> B)"
  (* TODO *)
  oops



section "Q4: Higer-Order Logic"

(*
You must use only these proof methods:
  - rule, erule, assumption, frule, drule,
    rule_tac, erule_tac, frule_tac, drule_tac, rename_tac, case_tac
You must use only these proof rules:
   - impI, impE, conjI, conjE, disjI1, disjI2, disjE, notI, notE
     iffI, iffE, iffD1, iffD2, ccontr, classical, FalseE,
     TrueI, conjunct1, conjunct2, mp;
   - allI, allE, exI, and exE
*)


lemma hol_a: "(\<forall>x. \<not> P x) = (\<not>(\<exists>x. P x))"
  (* TODO *)
  oops


lemma hol_b: "(\<exists>x y. P x y) = (\<exists>y x. P x y)"
  (* TODO *)
  oops


lemma hol_c: "(\<exists>x. P x \<longrightarrow> Q) = ((\<forall>x. P x) \<longrightarrow> Q)"
  (* TODO *)
  oops
  

lemma hol_d: "((\<forall>x. P x) \<longrightarrow> (\<exists>x. Q x)) = (\<exists>x. P x \<longrightarrow> Q x)"
  (* TODO *)
  oops


lemma hol_e: "\<forall>x.\<not>R x \<longrightarrow> R (M x) \<Longrightarrow> \<forall>x. R x \<or> R (M x)"
  (* TODO *)
  oops


lemma hol_f: "\<lbrakk>\<forall>x. \<not> R x \<longrightarrow> R (M x); \<exists>x. R x\<rbrakk> \<Longrightarrow> \<exists>x. R x \<and> R (M (M x))"
  (* TODO *)
  oops


end