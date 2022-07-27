(* IsageoCoq2_R1

Hilbert_Tarski_Model.thy

Version 2.2.0 IsaGeoCoq2_R1, Port part of GeoCoq 3.4.0
Copyright (C) 2021-2022 Roland Coghetto roland.coghetto ( a t ) cafr-msa2p.be
License: LGPGL

History
Version 1.0.0: IsaGeoCoq
Port part of GeoCoq 3.4.0 (https://geocoq.github.io/GeoCoq/) in Isabelle/Hol (Isabelle2021)

Copyright (C) 2021  Roland Coghetto roland_coghetto (at) hotmail.com

License: LGPL

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*)

(*<*)
theory Hilbert_Tarski_Model

imports Tarski_Neutral Tarski_2D Tarski_3D Tarski_Euclidean
  Tarski_Postulate_Parallels Hilbert

begin
  (*>*)

section "Hilbert - Tarski Model"

subsection "Tarski definition : model"

subsubsection "Definition"

definition (in Tarski_neutral_dimensionless) isLine:: "TPoint\<times>TPoint\<Rightarrow>bool" where
  "isLine l \<equiv> (fst l \<noteq> snd l)"

definition (in Tarski_neutral_dimensionless) Line :: "TPoint \<Rightarrow>TPoint \<Rightarrow>TPoint\<times>TPoint" where
  "Line A B = (if A \<noteq> B then (Pair A B) else undefined)"

definition (in Tarski_neutral_dimensionless) IncidentL ::"TPoint\<Rightarrow>TPoint\<times>TPoint\<Rightarrow>bool" where
  "IncidentL A l \<equiv> isLine l \<and> Col A (fst l) (snd l)"

definition (in Tarski_neutral_dimensionless) EqTL:: "TPoint\<times>TPoint\<Rightarrow>TPoint\<times>TPoint\<Rightarrow>bool" 
  ("_ =l= _" [99,99] 50) where
  "l1 =l= l2 \<equiv> isLine l1 \<and> isLine l2 \<and> (\<forall> X. (IncidentL X l1 \<longleftrightarrow> IncidentL X l2))"

definition  (in Tarski_neutral_dimensionless) Col_H:: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "Col_H A B C \<equiv> \<exists> l. (isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l)"

definition (in Tarski_neutral_dimensionless) isPlane :: "TPoint\<times>TPoint\<times>TPoint\<Rightarrow>bool" where
  "isPlane pl \<equiv> (\<forall> P Q R::TPoint. pl = (P,Q,R) \<longrightarrow> \<not> Col P Q R)"

definition (in Tarski_neutral_dimensionless) 
  Plane :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<times>TPoint\<times>TPoint" where
  "Plane A B C = (A,B,C)"

definition (in Tarski_neutral_dimensionless) IncidentP ::"TPoint\<Rightarrow>TPoint\<times>TPoint\<times>TPoint\<Rightarrow>bool" 
  where
    "IncidentP A pl \<equiv> (isPlane pl) \<and> (\<exists> P Q R. pl = Plane P Q R \<and> Coplanar A P Q R)"

definition (in Tarski_neutral_dimensionless) 
  EqTP:: "TPoint\<times>TPoint\<times>TPoint\<Rightarrow>TPoint\<times>TPoint\<times>TPoint\<Rightarrow>bool" ("_ =p= _" [99,99] 50) where
  "p1 =p= p2  \<equiv> isPlane p1 \<and> isPlane p2 \<and> (\<forall> X. (IncidentP X p1 \<longleftrightarrow> IncidentP X p2))"

definition (in Tarski_neutral_dimensionless) 
  IncidentLP ::"TPoint\<times>TPoint\<Rightarrow>TPoint\<times>TPoint\<times>TPoint\<Rightarrow>bool" where
  "IncidentLP l p \<equiv> isLine l \<and> isPlane p \<and> (\<forall> A. IncidentL A l \<longrightarrow> IncidentP A p)"

definition (in Tarski_neutral_dimensionless) Between_H :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "Between_H A B C \<equiv> Bet A B C \<and> A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C"

definition (in Tarski_neutral_dimensionless) cut_H :: "TPoint\<times>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "cut_H l A B \<equiv>  isLine l \<and> \<not> IncidentL A l \<and> \<not> IncidentL B l \<and> 
                  (\<exists> I. IncidentL I l \<and> Between_H A I B)"

definition (in Tarski_neutral_dimensionless) outH :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "outH P A B \<equiv> Between_H P A B \<or> Between_H P B A \<or> (P \<noteq> A \<and> A = B)"

definition (in Tarski_neutral_dimensionless) same_side_scott :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" 
  where "same_side_scott E A B \<equiv> E \<noteq> A \<and> E \<noteq> B \<and> Col_H E A B \<and> \<not> Between_H A E B"

definition (in Tarski_neutral_dimensionless) disjoint_H :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" 
  where "disjoint_H A B C D \<equiv> \<not> (\<exists> P. Between_H A P B \<and> Between_H C P D)"

definition (in Tarski_neutral_dimensionless) same_side_H :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<times>TPoint\<Rightarrow>bool" 
  where "same_side_H A B l \<equiv> isLine l \<and> (\<exists> P. cut_H l A P \<and> cut_H l B P)"

definition (in Tarski_neutral_dimensionless) same_side'_H :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" 
  where
    "same_side'_H A B X Y \<equiv> X \<noteq> Y \<and> (\<forall> l. isLine l \<and> (IncidentL X l \<and> IncidentL Y l) 
                                         \<longrightarrow> same_side_H A B l)"

definition (in Tarski_neutral_dimensionless) 
  CongA_H :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "CongA_H A B C D E F \<equiv> A B C CongA D E F"

definition (in Tarski_neutral_dimensionless) 
  Para_H :: "TPoint\<times>TPoint \<Rightarrow> TPoint\<times>TPoint \<Rightarrow>bool" where
  "Para_H l m \<equiv> isLine l \<and> isLine m \<and> (\<not>(\<exists> X. IncidentL X l \<and> IncidentL X m)) \<and> 
                                       (\<exists> p. IncidentLP l p \<and> IncidentLP m p)"

subsubsection "Propositions"

lemma (in Tarski_neutral_dimensionless) EqL__diff_left:
  assumes "l1 =l= l1" 
  shows "fst l1 \<noteq> snd l1" 
  using EqTL_def assms isLine_def by blast

lemma (in Tarski_neutral_dimensionless) EqL__diff_right:
  assumes "l1 =l= l2" 
  shows "(fst l2) \<noteq> (snd l2)" 
  using EqTL_def assms isLine_def by blast

context Tarski_neutral_dimensionless

begin

lemma axiom_line_existence:
  assumes "A \<noteq> B"
  shows "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l" 
proof -
  let ?l = "Pair A B"
  have "isLine ?l" 
    by (simp add: assms isLine_def)
  moreover have "IncidentL A ?l" 
    by (simp add: IncidentL_def \<open>isLine (A, B)\<close> col_trivial_1)
  moreover have "IncidentL B ?l" 
    by (simp add: IncidentL_def \<open>isLine (A, B)\<close> col_trivial_3)
  ultimately show ?thesis 
    by blast
qed

lemma incident_eq: 
  assumes "A \<noteq> B" and
    "IncidentL A l" and 
    "IncidentL B l"
  shows "Line A B =l= l" 
proof -
  have "Col A (fst l) (snd l)" 
    using IncidentL_def assms(2) by presburger
  have "Col B (fst l) (snd l)" 
    using IncidentL_def assms(3) by blast

  have "isLine (Line A B)" 
    by (simp add: Line_def assms(1) isLine_def)
  moreover have "isLine l" 
    using IncidentL_def assms(2) by blast
  {
    fix X
    assume "IncidentL X (Line A B)"
    hence "Col X A B" 
      by (simp add: IncidentL_def Line_def assms(1))
    have "Col X (fst l) (snd l)" 
      by (meson \<open>Col A (fst l) (snd l)\<close> \<open>Col B (fst l) (snd l)\<close> \<open>Col X A B\<close> 
          assms(1) col_permutation_1 colx)
    hence "IncidentL X l" 
      by (simp add: IncidentL_def \<open>isLine l\<close>)
  }
  moreover
  {
    fix X 
    assume "IncidentL X l" 
    have "Col X A B" 
      by (metis (no_types, lifting) IncidentL_def \<open>Col A (fst l) (snd l)\<close> 
          \<open>Col B (fst l) (snd l)\<close> \<open>IncidentL X l\<close> col_permutation_5 isLine_def l6_16_1)
    have "IncidentL X (Line A B)" 
      using IncidentL_def Line_def \<open>Col X A B\<close> assms(1) calculation(1) by auto
  }
  ultimately show ?thesis 
    using EqTL_def \<open>isLine l\<close> by blast
qed

lemma eq_transitivity: 
  assumes "l =l= m" and 
    "m =l= n"
  shows "l =l= n" 
  using EqTL_def assms(1) assms(2) by presburger

lemma eq_reflexivity: 
  assumes "isLine l"
  shows "l =l= l" 
  using EqTL_def assms by auto

lemma eq_symmetry:
  assumes "l =l= m"
  shows "m =l= l" 
  using EqTL_def assms by blast

(** The equality is compatible with IncidentL *)

lemma eq_incident: 
  assumes "l =l= m" 
  shows "IncidentL A l \<longleftrightarrow> IncidentL A m" 
  using EqTL_def assms by blast

lemma axiom_Incidl_morphism:
  assumes "IncidentL P l" and
    "l =l= m"
  shows "IncidentL P m" 
  using assms(1) assms(2) eq_incident by blast

(** There is only one line going through two points. *)

lemma axiom_line_uniqueness:
  assumes "A \<noteq> B" and
    "IncidentL A l" and "IncidentL B l" and
    "IncidentL A m" and "IncidentL B m" 
  shows "l =l= m" 
proof -
  have "Line A B =l= l" 
    by (simp add: assms(1) assms(2) assms(3) incident_eq)
  moreover have "Line A B =l= m" 
    by (simp add: assms(1) assms(4) assms(5) incident_eq)
  ultimately show ?thesis 
    using eq_symmetry eq_transitivity by blast
qed
  (** Every line contains at least two points. *)

lemma axiom_two_points_on_line: 
  assumes "isLine l"
  shows "\<exists> A B. IncidentL B l \<and> IncidentL A l \<and> A \<noteq> B" 
proof -
  let ?A = "fst l"
  let ?B = "snd l"
  have "IncidentL ?B l" 
    by (simp add: IncidentL_def assms col_trivial_3)
  moreover have "IncidentL ?A l" 
    by (simp add: IncidentL_def assms col_trivial_1)
  moreover have "?A \<noteq> ?B" 
    using assms isLine_def by blast
  ultimately show ?thesis 
    by blast
qed

(** We show that the notion of collinearity we just defined is equivalent to the
 notion of collinearity of Tarski. *)

lemma cols_coincide_1: 
  assumes "Col_H A B C"
  shows "Col A B C"  
proof -
  obtain l where "IncidentL A l" and "IncidentL B l" and "IncidentL C l"
    using Col_H_def assms by blast
  have "(fst l) \<noteq> (snd l)" 
    using IncidentL_def \<open>IncidentL B l\<close> isLine_def by blast
  have "Col A (fst l) (snd l)" 
    using IncidentL_def \<open>IncidentL A l\<close> by auto
  moreover have "Col B (fst l) (snd l)" 
    using IncidentL_def \<open>IncidentL B l\<close> by auto
  moreover have "Col C (fst l) (snd l)" 
    using IncidentL_def \<open>IncidentL C l\<close> by auto
  ultimately show ?thesis 
    by (metis \<open>fst l \<noteq> snd l\<close> col2__eq col_permutation_4 col_transitivity_1)
qed

lemma cols_coincide_2: 
  assumes "Col A B C"
  shows "Col_H A B C" 
proof (cases "A = B")
  case True
  thus ?thesis 
    by (metis Col_H_def axiom_line_existence diff_col_ex)
next
  case False
  let ?l = "Line A B"
  have "isLine ?l" 
    by (simp add: False Line_def isLine_def)
  moreover have "IncidentL A ?l" 
    using False IncidentL_def Line_def calculation col_trivial_1 by auto
  moreover have "IncidentL B ?l" 
    using False IncidentL_def Line_def calculation(1) col_trivial_3 by auto
  moreover have "IncidentL C ?l" 
    by (metis Col_perm False IncidentL_def Line_def assms calculation(1) 
        fst_def prod.simps(2) snd_def)
  ultimately show ?thesis 
    using Col_H_def by blast
qed

lemma cols_coincide: 
  shows "Col A B C \<longleftrightarrow> Col_H A B C" 
  using cols_coincide_1 cols_coincide_2 by blast

lemma ncols_coincide: 
  shows "\<not> Col A B C \<longleftrightarrow> \<not> Col_H A B C" 
  by (simp add: cols_coincide)

lemma lower_dim':
  shows "\<exists> PA PB PC. PA \<noteq> PB \<and> PB \<noteq> PC \<and>
 PA \<noteq> PC \<and> \<not> Col_H PA PB PC" 
  by (metis col_trivial_2 col_trivial_3 cols_coincide_1 not_col_exists 
      point_construction_different)

lemma axiom_plane_existence:
  assumes "\<not> Col_H A B C"
  shows "\<exists> p. IncidentP A p \<and> IncidentP B p \<and> IncidentP C p" 
proof -
  let ?p = "Plane A B C"
  have "isPlane ?p" 
    by (simp add: Plane_def assms isPlane_def ncols_coincide)
  have "IncidentP A ?p" 
    using IncidentP_def \<open>isPlane (Plane A B C)\<close> ncop_distincts by blast
  moreover have "IncidentP B ?p" 
    using IncidentP_def \<open>isPlane (Plane A B C)\<close> ncop_distincts by blast
  moreover have "IncidentP C ?p" 
    using IncidentP_def \<open>isPlane (Plane A B C)\<close> ncop_distincts by blast
  ultimately show ?thesis 
    by blast
qed

lemma incidentp_eqp:
  assumes "\<not> Col_H A B C"  and
    "IncidentP A p" and 
    "IncidentP B p" and
    "IncidentP C p" 
  shows "(Plane A B C) =p= p" 
proof -
  have "isPlane (Plane A B C)" 
    using Plane_def Tarski_neutral_dimensionless.cols_coincide_2 
      Tarski_neutral_dimensionless_axioms assms(1) isPlane_def by fastforce
  have "isPlane p" 
    using IncidentP_def assms(3) by blast
  obtain PA QA RA where "p = Plane PA QA RA" and 
    "Coplanar A PA QA RA" 
    using assms(2) IncidentP_def by blast
  hence "p = (PA,QA,RA)" 
    by (simp add: Plane_def)
  hence "Coplanar B PA QA RA" 
    using IncidentP_def Plane_def assms(3) by auto
  have "Coplanar C PA QA RA" 
    using IncidentP_def Plane_def assms(4) by (simp add: \<open>p = (PA, QA, RA)\<close>)
  have "\<not> Col PA QA RA" 
    using Plane_def \<open>isPlane p\<close> \<open>p = (PA, QA, RA)\<close> isPlane_def by blast
  have "\<not> Col A B C" 
    using Plane_def by (simp add: assms(1) ncols_coincide)
  {   
    fix X
    assume "IncidentP X (Plane A B C)"
    hence "isPlane (Plane A B C)" 
      by (simp add: \<open>isPlane (Plane A B C)\<close>)
    obtain  P Q R where "(Plane A B C) = Plane P Q R" and "Coplanar X P Q R" 
      using IncidentP_def \<open>IncidentP X (Plane A B C)\<close> by blast
    hence "A = P \<and> B = Q \<and> C = R" 
      using Plane_def by simp
    hence "Coplanar X A B C" 
      using \<open>Coplanar X P Q R\<close> by auto
    moreover
    have "Coplanar PA A B C" 
      by (meson \<open>Coplanar A PA QA RA\<close> \<open>Coplanar B PA QA RA\<close> \<open>Coplanar C PA QA RA\<close> 
          \<open>\<not> Col PA QA RA\<close> coplanar_perm_9 coplanar_pseudo_trans ncop_distincts)
    moreover have "Coplanar QA A B C" 
      by (meson \<open>Coplanar A PA QA RA\<close> \<open>Coplanar B PA QA RA\<close> \<open>Coplanar C PA QA RA\<close> 
          \<open>\<not> Col PA QA RA\<close> coplanar_perm_9 coplanar_pseudo_trans ncop_distincts)
    moreover have "Coplanar RA A B C" 
      by (meson \<open>Coplanar A PA QA RA\<close> \<open>Coplanar B PA QA RA\<close> \<open>Coplanar C PA QA RA\<close> 
          \<open>\<not> Col PA QA RA\<close> coplanar_perm_9 coplanar_pseudo_trans ncop_distincts)
    ultimately
    have "Coplanar X PA QA RA" 
      by (meson \<open>\<not> Col A B C\<close> coplanar_perm_9 coplanar_pseudo_trans)
    hence "\<exists> P Q R. p = Plane P Q R \<and> Coplanar X P Q R" 
      using \<open>p = Plane PA QA RA\<close> by blast
  } 
  moreover
  {
    fix X
    assume "IncidentP X p"
    hence "isPlane p" 
      by (simp add: \<open>isPlane p\<close>)
    obtain P Q R where "p = Plane P Q R" and
      "Coplanar X P Q R" 
      using IncidentP_def \<open>IncidentP X p\<close> by blast
    have "P = PA \<and> Q = QA \<and> R = RA" 
      using Plane_def \<open>p = (PA, QA, RA)\<close> \<open>p = Plane P Q R\<close> by auto
    hence "Coplanar X PA QA RA" 
      using \<open>Coplanar X P Q R\<close> by auto
    hence "Coplanar X A B C" 
      by (meson \<open>Coplanar A PA QA RA\<close> \<open>Coplanar B PA QA RA\<close> \<open>Coplanar C PA QA RA\<close> 
          \<open>\<not> Col PA QA RA\<close> coplanar_perm_9 coplanar_pseudo_trans)
    hence "IncidentP X (Plane A B C)" 
      using IncidentP_def \<open>isPlane (Plane A B C)\<close> by blast
  }
  ultimately show ?thesis 
    by (metis EqTP_def IncidentP_def \<open>isPlane (Plane A B C)\<close> \<open>isPlane p\<close>)
qed

(** Our equality is an equivalence relation. *)

lemma eqp_transitivity: 
  assumes "p =p= q" and 
    "q =p= r"
  shows "p =p= r" 
  using EqTP_def assms(1) assms(2) by presburger

lemma eqp_reflexivity: 
  assumes "isPlane p"
  shows "p =p= p" 
  by (simp add: EqTP_def assms)

lemma eqp_symmetry: 
  assumes "p =p= q"
  shows "q =p= p" 
  using EqTP_def assms by presburger

(** The equality is compatible with IncidentL *)

lemma eqp_incidentp: 
  assumes "p =p= q"
  shows "IncidentP A p \<longleftrightarrow> IncidentP A q" 
  using EqTP_def assms by blast

lemma axiom_Incidp_morphism :
  assumes "IncidentP M p" and
    "EqTP p q"
  shows "IncidentP M q" 
  using assms(1) assms(2) eqp_incidentp by blast

(** There is only one plane going through three non collinear points. *)

lemma axiom_plane_uniqueness: 
  assumes "\<not> Col_H A B C" and
    "IncidentP A p" and
    "IncidentP B p" and
    "IncidentP C p" and
    "IncidentP A q" and
    "IncidentP B q" and
    "IncidentP C q" 
  shows "p =p= q" 
proof -
  have "Plane A B C =p= p"   
    using assms(1) assms(2) assms(3) assms(4) incidentp_eqp by auto
  moreover have "Plane A B C =p= q"   
    using assms(1) assms(5) assms(6) assms(7) incidentp_eqp by auto
  ultimately show ?thesis
    using eqp_symmetry eqp_transitivity by blast
qed

(** Every plane contains at least one point. *)

lemma axiom_one_point_on_plane:
  assumes "isPlane p"
  shows "\<exists> A. IncidentP A p" 
proof -
  obtain A B C where "p = Plane A B C" 
    by (metis Plane_def surj_pair)
  thus ?thesis 
    using IncidentP_def assms coplanar_trivial by blast
qed

lemma axiom_line_on_plane:
  assumes "A \<noteq> B" and
    "IncidentL A l" and 
    "IncidentL B l" and 
    "IncidentP A p" and
    "IncidentP B p"
  shows "IncidentLP l p" 
proof -
  have "isLine l \<and> Col A (fst l) (snd l)" 
    using IncidentL_def assms(2) by blast
  let ?U = "(fst l)"
  let ?V = "(snd l)"
  have "l = Line ?U ?V" 
    by (metis IncidentL_def Line_def assms(2) isLine_def prod.exhaust_sel)
  hence "Col A ?U ?V" 
    by (metis IncidentL_def assms(2))
  have "Col B ?U ?V" 
    by (metis IncidentL_def assms(3))
  have "isLine l" 
    using IncidentL_def assms(3) by blast
  hence "fst l \<noteq> snd l" 
    by (simp add: isLine_def)
  hence "?U \<noteq> ?V"
    by blast
  have "Col A B ?U" 
    using \<open>Col A (fst l) (snd l)\<close> \<open>Col B (fst l) (snd l)\<close> \<open>fst l \<noteq> snd l\<close> 
      col2__eq col_permutation_5 by blast
  have "Col A B ?V" 
    by (metis Col_cases \<open>Col A B (fst l)\<close> \<open>Col A (fst l) (snd l)\<close> 
        \<open>Col B (fst l) (snd l)\<close> col_transitivity_1)
  obtain PA QA RA where "p = Plane PA QA RA" and "Coplanar A PA QA RA" 
    using IncidentP_def assms(4) by blast
  hence "\<not> Col PA QA RA" 
    using IncidentP_def Plane_def assms(4) isPlane_def by blast
  obtain PB QB RB where "p = Plane PB QB RB" and "Coplanar B PB QB RB" 
    using IncidentP_def assms(5) by blast
  hence "\<not> Col PB QB RB" 
    using IncidentP_def Plane_def assms(5) isPlane_def by auto
  have "Coplanar B PA QA RA" 
    using Plane_def \<open>Coplanar B PB QB RB\<close> \<open>p = Plane PA QA RA\<close> \<open>p = Plane PB QB RB\<close> by force
  have "Coplanar ?U PA QA RA" 
    using \<open>Coplanar A PA QA RA\<close> \<open>Coplanar B PA QA RA\<close> 
      ncoplanar_perm_23 \<open>Col A B (fst l)\<close> assms(1) col_cop2__cop by blast
  have "Coplanar ?V PA QA RA" 
    by (meson ncoplanar_perm_23 \<open>Col A B (snd l)\<close> \<open>Coplanar A PA QA RA\<close> 
        \<open>Coplanar B PA QA RA\<close> assms(1) col_cop2__cop)
  have "isLine l" 
    using IncidentL_def assms(3) by blast
  moreover have "isPlane p" 
    using IncidentP_def assms(5) by blast
  moreover
  {
    fix A'
    assume "IncidentL A' l"
    hence "Col A' ?U ?V" 
      using IncidentL_def by blast
    have "Coplanar A' PA QA RA" 
      by (meson ncoplanar_perm_23 IncidentL_def \<open>Coplanar (fst l) PA QA RA\<close> 
          \<open>Coplanar (snd l) PA QA RA\<close> \<open>IncidentL A' l\<close> 
          col_cop2__cop isLine_def not_col_permutation_2)
    hence "\<exists> P Q R. p = Plane P Q R \<and> Coplanar A' P Q R" 
      using \<open>p = Plane PA QA RA\<close> by blast
    hence "IncidentP A' p" 
      by (simp add: IncidentP_def calculation(2))
  }
  ultimately show ?thesis
    using IncidentLP_def by blast
qed

(** * Group II Order *)

(** Definition of the Between predicate of Hilbert.
    Note that it is different from the Between of Tarski.
    The Between of Hilbert is strict. *)

lemma axiom_between_col:
  assumes "Between_H A B C"
  shows "Col_H A B C" 
  using Between_H_def Col_def assms cols_coincide_2 by presburger

lemma axiom_between_diff:
  assumes "Between_H A B C"
  shows "A \<noteq> C" 
  using Between_H_def assms by auto

(** If B is between A and C, it is also between C and A. *)

lemma axiom_between_comm: 
  assumes "Between_H A B C"
  shows "Between_H C B A" 
  by (metis Between_H_def assms between_symmetry)

lemma axiom_between_out:
  assumes "A \<noteq> B" 
  shows "\<exists> C. Between_H A B C" 
  by (metis Between_H_def assms bet_neq12__neq point_construction_different)

lemma axiom_between_only_one:
  assumes "Between_H A B C"
  shows "\<not> Between_H B C A" 
  by (metis Bet_cases Between_H_def assms between_equality)

lemma between_one:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "Col A B C" 
  shows "Between_H A B C \<or> Between_H B C A \<or> Between_H B A C" 
  using Bet_cases Between_H_def Col_def assms(1) assms(2) assms(3) assms(4) by auto

lemma axiom_between_one:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "Col_H A B C" 
  shows "Between_H A B C \<or> Between_H B C A \<or> Between_H B A C" 
  by (simp add: assms(1) assms(2) assms(3) assms(4) between_one cols_coincide_1)


(** Axiom of Pasch, (Hilbert version). *)

(** First we define a predicate which means that the line l intersects the segment AB. *)


(** We show that this definition is equivalent to the predicate TS of Tarski. *)

lemma cut_two_sides: 
  shows "cut_H l A B \<longleftrightarrow> (fst l) (snd l) TS A B"
proof -
  {
    assume "cut_H l A B"
    have "(fst l) (snd l) TS A B" 
      by (meson Between_H_def TS_def IncidentL_def \<open>cut_H l A B\<close> cut_H_def)
  }
  moreover
  {
    assume "(fst l) (snd l) TS A B"
    then obtain T where "Col T (fst l) (snd l)" and "Bet A T B" 
      using TS_def by blast
    have "\<not> IncidentL A l" 
      using IncidentL_def TS_def \<open>(fst l) (snd l) TS A B\<close> by auto
    moreover have "\<not> IncidentL B l" 
      using IncidentL_def TS_def \<open>(fst l) (snd l) TS A B\<close> by blast
    moreover have "\<exists> I. isLine l \<and> IncidentL I l \<and> Between_H A I B" 
      by (metis Between_H_def IncidentL_def TS_def \<open>(fst l) (snd l) TS A B\<close> 
          isLine_def ts_distincts)
    ultimately have "cut_H l A B"
      using cut_H_def by presburger
  }
  ultimately show ?thesis 
    by blast
qed

lemma cop_plane_aux: 
  assumes "Coplanar A B C D" and 
    "A \<noteq> B" 
  shows "\<exists> p. IncidentP A p \<and> IncidentP B p \<and> IncidentP C p \<and> IncidentP D p" 
proof -
  obtain X where "(Col A B X \<and> Col C D X) \<or>
            (Col A C X \<and> Col B D X) \<or>
            (Col A D X \<and> Col B C X)" 
    using Coplanar_def assms(1) by auto
  {
    assume "Col A B C"
    have "\<exists> p. IncidentP A p \<and> IncidentP B p \<and> IncidentP C p \<and> IncidentP D p" 
    proof (cases "Col A B D")
      case True
      hence "Col A B D" 
        by blast
      obtain E where "\<not> Col A B E" 
        using assms(2) not_col_exists by auto
      hence "\<not> Col_H A B E" 
        using cols_coincide_1 by blast
      let ?p = "Plane A B E" 
      have "IncidentP A ?p" 
        using EqTP_def \<open>\<not> Col_H A B E\<close> axiom_plane_existence incidentp_eqp by blast
      moreover have "IncidentP B ?p" 
        using IncidentP_def calculation ncop_distincts by blast
      moreover have "IncidentP C ?p" 
        by (meson Col_cases IncidentP_def \<open>Col A B C\<close> calculation(1) ncop__ncols)
      moreover have "IncidentP D ?p" 
        by (meson Col_cases IncidentP_def True calculation(3) ncop__ncols)
      ultimately show ?thesis 
        by blast
    next
      case False
      hence "\<not> Col_H A B D" 
        using cols_coincide_1 by blast
      let ?p = "Plane A B D" 
      have "IncidentP A ?p" 
        by (meson EqTP_def \<open>\<not> Col_H A B D\<close> axiom_plane_existence incidentp_eqp)
      moreover have "IncidentP B ?p" 
        using IncidentP_def calculation ncop_distincts by blast
      moreover have "IncidentP C ?p" 
        using IncidentP_def assms(1) calculation(1) coplanar_perm_12 by blast
      moreover have "IncidentP D ?p" 
        using IncidentP_def calculation(3) ncop_distincts by blast
      ultimately show ?thesis 
        by blast
    qed
  }
  moreover
  {
    assume "\<not> Col A B C"
    let ?p = "Plane A B C"
    have "IncidentP A ?p" 
      by (simp add: IncidentP_def Plane_def \<open>\<not> Col A B C\<close> coplanar_trivial isPlane_def)
    moreover have "IncidentP B ?p" 
      using IncidentP_def calculation ncop_distincts by blast
    moreover have "IncidentP C ?p" 
      using IncidentP_def calculation(2) ncop_distincts by blast
    moreover have "IncidentP D ?p" 
      using IncidentP_def assms(1) calculation(3) coplanar_perm_18 by blast
    ultimately have "\<exists> p. IncidentP A p \<and> IncidentP B p \<and> IncidentP C p \<and> IncidentP D p" 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma cop_plane:
  assumes "Coplanar A B C D"
  shows "\<exists> p. IncidentP A p \<and> IncidentP B p \<and> IncidentP C p \<and> IncidentP D p" 
  by (metis assms cop_plane_aux coplanar_trivial diff_col_ex ncoplanar_perm_22)

lemma plane_cop:
  assumes "IncidentP A p" and 
    "IncidentP B p" and
    "IncidentP C p" and
    "IncidentP D p" 
  shows "Coplanar A B C D" 
proof -
  obtain PA QA RA where "p = Plane PA QA RA" and "Coplanar A PA QA RA" 
    using IncidentP_def assms(1) by auto
  hence "p = (PA,QA,RA)" 
    using Plane_def by blast
  moreover
  obtain PB QB RB where "p = Plane PB QB RB" and "Coplanar B PB QB RB" 
    using IncidentP_def assms(2) by auto
  hence "p = (PB,QB,RB)" 
    using Plane_def by blast
  moreover
  obtain PC QC RC where "p = Plane PC QC RC" and "Coplanar C PC QC RC" 
    using IncidentP_def assms(3) by auto
  hence "p = (PC,QC,RC)" 
    using Plane_def by blast
  moreover
  obtain PD QD RD where "p = Plane PD QD RD" and "Coplanar D PD QD RD" 
    using IncidentP_def assms(4) by auto
  hence "p = (PD,QD,RD)" 
    using Plane_def by blast
  ultimately have "Coplanar B PA QA RA \<and> Coplanar C PA QA RA \<and> Coplanar D PA QA RA" 
    using \<open>Coplanar B PB QB RB\<close> \<open>Coplanar C PC QC RC\<close> \<open>Coplanar D PD QD RD\<close> by fastforce
  have "isPlane p" 
    using IncidentP_def assms(1) by blast
  hence "\<not> Col PA QA RA" 
    using isPlane_def \<open>p = (PA, QA, RA)\<close> by blast
  thus ?thesis 
    by (meson \<open>Coplanar A PA QA RA\<close> coplanar_perm_18 coplanar_pseudo_trans
        \<open>Coplanar B PA QA RA \<and> Coplanar C PA QA RA \<and> Coplanar D PA QA RA\<close> )
qed

lemma axiom_pasch:
  assumes "\<not> Col_H A B C" and
    "IncidentP A p" and 
    "IncidentP B p" and 
    "IncidentP C p" and
    "IncidentLP l p" and
    "\<not> IncidentL C l" and
    "cut_H l A B"
  shows "cut_H l A C \<or> cut_H l B C" 
proof -
  let ?A = "(fst l)"
  let ?B = "(snd l)"
  have "?A ?B TS A B" 
    using assms(7) cut_two_sides by auto
  hence 1: "\<not> Col A ?A ?B \<and> \<not> Col B ?A ?B \<and> (\<exists> T. Col T ?A ?B \<and> Bet A T B)"
    using TS_def by blast
  hence "\<not> Col A ?A ?B" 
    by blast
  have "\<not> Col B ?A ?B" 
    by (simp add: 1)
  obtain T where "Col T ?A ?B" and "Bet A T B" 
    using 1 by auto
  have "\<not> Col A B C" 
    using assms(1) cols_coincide_2 by blast
  have "\<not> Col C ?A ?B" 
    using IncidentLP_def IncidentL_def assms(5) assms(6) by blast
  have "Coplanar ?A ?B A C"
  proof (rule plane_cop, insert assms(2) assms(4))
    show "IncidentP (fst l) p" 
      using IncidentLP_def IncidentL_def assms(5) col_trivial_1 by blast
    show "IncidentP (snd l) p" 
      using IncidentLP_def IncidentL_def assms(5) col_trivial_3 by blast
  qed
  have "?A ?B TS A C \<or> ?A ?B OS A C" 
    using \<open>Coplanar ?A ?B A C\<close> 1 \<open>\<not> Col C ?A ?B\<close> cop_nos__ts by blast
  moreover
  {
    assume "?A ?B TS A C" 
    have "cut_H l A C \<or> cut_H l B C" 
      by (simp add: \<open>?A ?B TS A C\<close> cut_two_sides)
  } 
  moreover
  {
    assume "?A ?B OS A C" 
    have "cut_H l A C \<or> cut_H l B C" 
      using \<open>?A ?B OS A C\<close> \<open>?A ?B TS A B\<close> cut_two_sides l9_2 l9_8_2 by blast
  } 
  ultimately show ?thesis
    by blast
qed

lemma Incid_line:
  assumes "A \<noteq> B" and
    "IncidentL A l" and
    "IncidentL B l" and
    "Col P A B"
  shows "IncidentL P l" 
  by (meson Col_H_def assms(1) assms(2) assms(3) assms(4) cols_coincide_2 
      eq_incident incident_eq)

(** * Group III Congruence *)

(** The cong predicate of Hilbert is the same as the one of Tarski: *)

lemma out_outH: 
  assumes "P Out A B" 
  shows "outH P A B" 
  using Between_H_def Out_def assms outH_def by auto

lemma axiom_hcong_1_existence:
  assumes "A \<noteq> B" and
    "A' \<noteq> P" and
    "IncidentL A' l" and
    "IncidentL P l" 
  shows "\<exists> B'. IncidentL B' l \<and> outH A' P B' \<and> Cong A' B' A B"
proof -
  obtain B' where "A' Out B' P \<and> Cong A' B' A B" 
    using assms(1) assms(2) l6_11_existence by presburger
  have "IncidentL B' l" 
    using Col_perm Incid_line \<open>A' Out B' P \<and> Cong A' B' A B\<close> assms(2) assms(3) 
      assms(4) out_col by blast
  moreover have "outH A' P B'" 
    by (simp add: \<open>A' Out B' P \<and> Cong A' B' A B\<close> l6_6 out_outH)
  ultimately show ?thesis 
    using \<open>A' Out B' P \<and> Cong A' B' A B\<close> by blast
qed

lemma axiom_hcong_1_uniqueness:
  assumes (*"A \<noteq> B" and*)
    "IncidentL M l" and
    "IncidentL A' l" and 
    (*"IncidentL B' l" and*)
    "IncidentL A'' l" and
    (*"IncidentL B'' l" and*)
    "Between_H A' M B'" and
    "Cong M A' A B" and
    "Cong M B' A B" and
    "Between_H A'' M B''" and
    "Cong M A'' A B" and
    "Cong M B'' A B"
  shows "(A' = A'' \<and> B' = B'') \<or> (A' = B'' \<and> B' = A'')" 
proof -
  let ?A = "fst l"
  let ?B = "snd l"
  have "A'' \<noteq> M" 
    using Between_H_def assms(7)by blast
  {
    assume "M Out A' A''"
    have "M Out A'' A''" 
      by (simp add: \<open>A'' \<noteq> M\<close> out_trivial)
    hence "A' = A''" 
      using l6_11_uniqueness \<open>M Out A' A''\<close> assms(5) assms(8) by blast
    hence "A' = A'' \<and> B' = B''" 
      by (metis Between_H_def assms(7) assms(9) assms(4) assms(6) construction_uniqueness)
  }
  moreover
  {
    assume "\<not> M Out A' A''"
    have "Col A' M A''" 
      using col3 [where ?X = "?A" and ?Y = "?B"] 
      by (meson Col_H_def IncidentL_def assms(1) assms(2) assms(3) ncols_coincide)
    hence "Bet A' M A''" 
      using not_out_bet \<open>\<not> M Out A' A''\<close> by blast
    have "A' = B''" 
      by (metis Between_H_def \<open>Bet A' M A''\<close> assms(7) assms(9) assms(5) 
          between_symmetry construction_uniqueness)
    hence "A' = B'' \<and> B' = A''" 
      by (metis Between_H_def \<open>Bet A' M A''\<close> assms(8) assms(4) assms(6) construction_uniqueness)
  }
  ultimately show ?thesis
    by blast
qed

(** As a remark we also prove another version of this axiom as formalized in Isabelle by
Phil Scott. *)

lemma axiom_hcong_scott:
  assumes "A \<noteq> C" and 
    "P \<noteq> Q"
  shows "\<exists> B. same_side_scott A B C \<and> Cong P Q A B"
proof -
  obtain X where "A Out X C" and "Cong A X P Q" 
    using assms(1) assms(2) l6_11_existence by metis
  have "A \<noteq> X" 
    using \<open>A Out X C\<close> l6_3_1 by blast
  moreover have "Col_H A X C" 
    by (simp add: \<open>A Out X C\<close> cols_coincide_2 out_col)
  moreover have "\<not> Between_H X A C" 
    using Between_H_def \<open>A Out X C\<close> not_bet_and_out by force
  moreover have "Cong P Q A X" 
    using Cong_cases \<open>Cong A X P Q\<close> by blast
  ultimately show ?thesis
    using assms(1) same_side_scott_def by blast
qed

(** We define when two segments do not intersect. *)


(** Note that two disjoint segments may share one of their extremities. *)

lemma col_disjoint_bet:
  assumes "Col_H A B C" and
    "disjoint_H A B B C"
  shows "Bet A B C" 
proof -
  have "Col A B C" 
    by (simp add: assms(1) cols_coincide_1)
  show ?thesis 
  proof (cases "A = B")
    case True
    thus ?thesis 
      by (simp add: between_trivial2)
  next
    case False
    hence "A \<noteq> B" 
      by blast
    show ?thesis 
    proof (cases "B = C")
      case True
      thus ?thesis 
        by (simp add: between_trivial)
    next
      case False
      hence "B \<noteq> C" 
        by blast
      {
        assume "Bet B C A"
        obtain M where "M Midpoint B C" 
          using midpoint_existence by blast
        have "Between_H A M B" 
          by (metis Between_H_def False Midpoint_def \<open>A \<noteq> B\<close> \<open>Bet B C A\<close> 
              \<open>M Midpoint B C\<close> axiom_between_comm between_equality_2 between_exchange4
              midpoint_not_midpoint midpoint_out out_diff1)
        moreover have "Between_H B M C" 
          by (metis Between_H_def False Midpoint_def \<open>M Midpoint B C\<close> 
              calculation is_midpoint_id_2)
        ultimately have "\<exists> P. Between_H A P B \<and> Between_H B P C" 
          by blast
        hence False 
          using assms(2) disjoint_H_def by blast
      }
      moreover
      {
        assume "Bet C A B"
        obtain M where "M Midpoint A B"
          using midpoint_existence by blast
        have "Between_H A M B" 
          by (metis Between_H_def \<open>A \<noteq> B\<close> \<open>M Midpoint A B\<close> midpoint_bet midpoint_distinct_1)
        moreover have "Between_H B M C" 
          by (metis Bet_cases Between_H_def False \<open>Bet B C A \<Longrightarrow> False\<close> \<open>Bet C A B\<close> 
              between_exchange2 calculation)
        ultimately
        have "\<exists> P. Between_H A P B \<and> Between_H B P C" 
          by blast
        hence False  
          using assms(2) disjoint_H_def by blast
      }
      ultimately show ?thesis 
        using \<open>Col A B C\<close> Col_def by blast
    qed
  qed
qed

lemma axiom_hcong_3:
  assumes "Col_H A B C" and
    "Col_H A' B' C'" and
    "disjoint_H A B B C" and
    "disjoint_H A' B' B' C'" and
    "Cong A B A' B'" and
    "Cong B C B' C'"
  shows "Cong A C A' C'" 
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) col_disjoint_bet l2_11_b)

lemma exists_not_incident: 
  assumes "A \<noteq> B" 
  shows "\<exists> C. \<not> IncidentL C (Line A B)" 
  using Col_H_def IncidentL_def lower_dim' by blast

(** Same side predicate corresponds to OS of Tarski. *)

lemma same_side_one_side: 
  assumes "same_side_H A B l"
  shows "(fst l) (snd l) OS A B" 
  by (meson OS_def cut_two_sides assms same_side_H_def)

lemma one_side_same_side: 
  assumes "(fst l)(snd l) OS A B"
  shows "same_side_H A B l"
proof -
  have "isLine l" 
    using assms isLine_def os_distincts by presburger
  thus ?thesis
    using OS_def assms cut_two_sides same_side_H_def by presburger
qed

lemma OS_distinct:
  assumes "P Q OS A B"
  shows "P \<noteq> Q" 
  using assms os_distincts by auto

lemma OS_same_side':
  assumes "P Q OS A B"
  shows "same_side'_H A B P Q" 
proof -
  have "P \<noteq> Q" 
    using assms os_distincts by blast
  moreover
  {
    fix l
    assume "IncidentL P l" and
      "IncidentL Q l"
    hence "isLine l" 
      using IncidentL_def by auto
    have "(fst l) \<noteq> (snd l)" 
      using \<open>isLine l\<close> isLine_def by auto
    have "Col P (fst l) (snd l)" 
      using IncidentL_def \<open>IncidentL P l\<close> by auto
    have "Col Q (fst l) (snd l)" 
      using IncidentL_def \<open>IncidentL Q l\<close> by auto
    have "(fst l) (snd l) OS A B" 
      by (metis (no_types, lifting) \<open>Col P (fst l) (snd l)\<close> \<open>Col Q (fst l) (snd l)\<close> 
          \<open>(fst l) \<noteq> (snd l)\<close> assms col2_os__os l6_16_1 not_col_permutation_5)
    hence "same_side_H A B l" 
      using one_side_same_side by blast
  }
  ultimately show ?thesis 
    using same_side'_H_def by auto
qed

lemma same_side_OS:
  assumes "same_side'_H P Q A B"
  shows "A B OS P Q" 
proof -
  obtain X where "IncidentL A X" and "IncidentL B X" 
    using assms axiom_line_existence same_side'_H_def by blast
  hence "same_side_H P Q X" 
    using EqTL_def assms incident_eq same_side'_H_def by blast
  thus ?thesis
    by (metis IncidentL_def assms axiom_line_existence col2_os__os col_permutation_1 
        same_side'_H_def same_side_one_side)
qed

(** This is equivalent to the out predicate of Tarski. *)

lemma outH_out: 
  assumes "outH P A B"
  shows "P Out A B" 
  using Between_H_def Out_def assms outH_def out_trivial by force

(** The 2D version of the fourth congruence axiom **)

lemma incident_col: 
  assumes "IncidentL M l"
  shows "Col M (fst l)(snd l)" 
  using IncidentL_def assms by auto

lemma col_incident:
  assumes "(fst l) \<noteq> (snd l)" and (** ROLL: EXPLICIT ADD **)
    "Col M (fst l)(snd l)"
  shows "IncidentL M l"   
  by (simp add: IncidentL_def assms(1) assms(2) isLine_def)

lemma Bet_Between_H: 
  assumes "Bet A B C" and
    "A \<noteq> B" and
    "B \<noteq> C" 
  shows "Between_H A B C" 
  using Between_H_def assms(1) assms(2) assms(3) bet_neq12__neq by presburger

lemma axiom_cong_5':
  assumes (*"\<not> Col_H A B C" and*)
    "\<not> Col_H A' B' C'" and
    "Cong A B A' B'" and
    "Cong A C A' C'" and
    "B A C CongA B' A' C'"
  shows "A B C CongA A' B' C'" 
  by (metis assms(2) assms(3) assms(4) assms(1) cols_coincide_2 cong_diff_4 
      l11_49 not_col_distincts)

lemma axiom_cong_5'_bis:
  assumes "\<not> Col_H A B C" and
    (*"\<not> Col_H A' B' C'" and*)
    "Cong A B A' B'" and
    "Cong A C A' C'" and
    "B A C CongA B' A' C'"
  shows "A B C CongA A' B' C'" 
  using assms(1) assms(3) assms(4) assms(2) col_trivial_2 cols_coincide_2 l11_49 by blast

lemma axiom_hcong_4_existence:
  assumes "\<not> Col_H P PO X" and
    "\<not> Col_H A B C" 
  shows "\<exists> Y. (A B C CongA X PO Y \<and> same_side'_H P Y PO X)" 
proof -
  have "\<not> Col P PO X"   
    by (simp add: assms(1) ncols_coincide)
  have "\<not> Col A B C"   
    using assms(2) cols_coincide_2 by blast
  have "\<not> Col X PO P" 
    using \<open>\<not> Col P PO X\<close> not_col_permutation_3 by blast
  obtain Y where "A B C CongA X PO Y" and "X PO OS Y P" 
    using \<open>\<not> Col A B C\<close> \<open>\<not> Col X PO P\<close> angle_construction_1 by blast
  thus ?thesis 
    using OS_same_side' invert_one_side one_side_symmetry by blast
qed

lemma same_side_trans:
  assumes "same_side_H A B l" and
    "same_side_H B C l"
  shows "same_side_H A C l" 
  using assms(1) assms(2) one_side_same_side one_side_transitivity same_side_one_side by blast

lemma same_side_sym:
  assumes "same_side_H A B l"
  shows "same_side_H B A l" 
  by (meson assms same_side_H_def)

lemma axiom_hcong_4_uniqueness:
  assumes "\<not> Col_H P PO X" and
    "\<not> Col_H A B C" and
    "A B C CongA X PO Y" and
    "A B C CongA X PO Y'" and
    "same_side'_H P Y PO X" and
    "same_side'_H P Y' PO X"
  shows "outH PO Y Y'" 
proof -
  have "\<not> Col P PO X"   
    using assms(1) cols_coincide_2 by blast
  have "\<not> Col A B C"   
    using assms(2) cols_coincide_2 by blast
  have "X PO Y CongA X PO Y'" 
    using assms(3) assms(4) conga_sym not_conga by blast
  moreover
  have "X PO OS Y Y'" 
    by (meson assms(5) assms(6) invert_one_side one_side_symmetry 
        one_side_transitivity same_side_OS)
  ultimately have "PO Out Y Y'" 
    by (simp add: conga_os__out)
  thus ?thesis 
    by (simp add: out_outH)
qed

lemma axiom_conga_comm:
  assumes "\<not> Col_H A B C" 
  shows "A B C CongA C B A" 
  by (metis assms col_trivial_1 col_trivial_2 cols_coincide_2 conga_pseudo_refl)

lemma axiom_congaH_outH_congaH:
  assumes "A B C CongA D E F" and
    "Between_H B A A' \<or> Between_H B A' A \<or> B \<noteq> A \<and> A = A'" and
    "Between_H B C C' \<or> Between_H B C' C \<or> B \<noteq> C \<and> C = C'" and
    "Between_H E D D' \<or> Between_H E D' D \<or> E \<noteq> D \<and> D = D'" and
    "Between_H E F F' \<or> Between_H E F' F \<or> E \<noteq> F \<and> F = F'"
  shows "A' B C' CongA D' E F'" 
proof (rule l11_10 [where ?A = "A" and ?C = "C" and ?D = "D" and ?F = "F"], insert assms(1))
  show "B Out A' A" 
    using Between_H_def Out_def assms(2) out_trivial by force
  show "B Out C' C" 
    using assms(3) outH_def outH_out by blast
  show "E Out D' D" 
    using assms(4) outH_def outH_out by blast
  show "E Out F' F" 
    using assms(5) outH_def outH_out by blast
qed

lemma axiom_conga_permlr:
  assumes "A B C CongA D E F"
  shows "C B A CongA F E D" 
  by (simp add: assms conga_comm)

lemma axiom_conga_refl: 
  assumes "\<not> Col_H A B C"
  shows "A B C CongA A B C" 
  using assms axiom_conga_comm conga_right_comm by blast

end

lemma (in Tarski_3D) not_coplanar_S1_S2_S3_S4:
  shows "\<not> Coplanar TS1 TS2 TS3 TS4" 
proof -
  {
    assume "Coplanar TS1 TS2 TS3 TS4"
    then obtain X where "(Col TS1 TS2 X \<and> Col TS3 TS4 X) \<or>
            (Col TS1 TS3 X \<and> Col TS2 TS4 X) \<or>
            (Col TS1 TS4 X \<and> Col TS2 TS3 X)" 
      using Coplanar_def by auto
    hence False using lower_dim_3 Col_def by blast
  }
  thus ?thesis 
    by blast
qed

lemma (in Tarski_3D) lower_dim_3':
  shows "\<not> (\<exists> p. isPlane p \<and> IncidentP TS1 p \<and> IncidentP TS2 p \<and> 
                              IncidentP TS3 p \<and> IncidentP TS4 p)" 
proof -
  {
    assume "\<exists> p. isPlane p \<and> IncidentP TS1 p \<and> IncidentP TS2 p \<and> 
                             IncidentP TS3 p \<and> IncidentP TS4 p"
    then obtain p where "isPlane p" and "IncidentP TS1 p" and "IncidentP TS2 p" and
      "IncidentP TS3 p \<and> IncidentP TS4 p"
      by blast
    hence "Coplanar TS1 TS2 TS3 TS4" 
      using plane_cop by blast
    hence False using not_coplanar_S1_S2_S3_S4 by simp
  }
  thus ?thesis 
    by blast
qed

lemma (in Tarski_Euclidean) Para_Par:
  assumes "A \<noteq> B" and 
    "C \<noteq> D" and
    "Para_H (Line A B) (Line C D)"
  shows "A B Par C D" 
proof -
  have "isLine (Line A B)" 
    using assms(3) Para_H_def by blast
  have "isLine (Line C D)" 
    using assms(3) Para_H_def by blast
  have 1: "(\<not>(\<exists> X. IncidentL X (Line A B) \<and> IncidentL X (Line C D))) \<and> 
(\<exists> p. IncidentLP (Line A B) p \<and> IncidentLP (Line C D) p)"
    using assms(3) Para_H_def by blast
  then obtain p where "IncidentLP (Line A B) p" and "IncidentLP (Line C D) p" 
    by blast
  have "Coplanar A B C D" 
  proof -
    have "IncidentP A p" 
      using IncidentLP_def \<open>IncidentLP (Line A B) p\<close> assms(1) axiom_line_existence 
        eq_incident incident_eq by blast
    moreover have "IncidentP B p" 
      using IncidentLP_def \<open>IncidentLP (Line A B) p\<close> assms(1) axiom_line_existence 
        eq_incident incident_eq by blast
    moreover have "IncidentP C p" 
      using IncidentLP_def \<open>IncidentLP (Line C D) p\<close> assms(2) axiom_line_existence 
        eq_incident incident_eq by blast
    moreover have "IncidentP D p" 
      using IncidentLP_def \<open>IncidentLP (Line C D) p\<close> assms(2) axiom_line_existence 
        eq_incident incident_eq by blast
    ultimately show ?thesis
      by (simp add: plane_cop)
  qed
  moreover
  {
    assume "\<exists> X. Col X A B \<and> Col X C D"
    then obtain X where "Col X A B" and "Col X C D" 
      by blast
    hence "Col_H X A B"  
      by (simp add: cols_coincide_2)
    hence "IncidentL X (Line A B)" 
      using assms(1) IncidentL_def Col_H_def by (meson EqTL_def incident_eq)
    moreover
    have "Col_H X C D" 
      using cols_coincide_2 by (simp add: \<open>Col X C D\<close>)
    hence "IncidentL X (Line C D)" 
      using assms(2) IncidentL_def Col_H_def eq_incident incident_eq by blast
    ultimately have False 
      using 1 by blast
  }
  hence "\<not> (\<exists> X. Col X A B \<and> Col X C D)" 
    by blast
  ultimately show ?thesis 
    using Par_def by (meson cop_npar__inter_exists) 
qed

lemma (in Tarski_Euclidean) axiom_euclid_uniqueness:
  assumes "\<not> IncidentL P l" and
    "Para_H l m1" and
    "IncidentL P m1" and
    "Para_H l m2" and
    "IncidentL P m2"
  shows "m1 =l= m2" 
proof -
  let ?A = "fst l"
  let ?B = "snd l"
  let ?C = "fst m1"
  let ?D = "snd m1"
  let ?C' = "fst m2"
  let ?D' = "snd m2"
  have "l = Line ?A ?B" 
    using Line_def Para_H_def assms(4) isLine_def by auto
  have "m1 = Line ?C ?D" 
    using Line_def Para_H_def assms(2) isLine_def by auto
  have "m2 = Line ?C' ?D'" 
    using Line_def Para_H_def assms(4) isLine_def by auto
  have "\<not> Col P ?A ?B" 
    using IncidentL_def Para_H_def assms(1) assms(4) by blast
  have "Para_H (Line ?A ?B) (Line ?C ?D)" 
    using assms(2) \<open>l = Line (fst l) (snd l)\<close> \<open>m1 = Line (fst m1) (snd m1)\<close> by force
  have "Para_H (Line ?A ?B) (Line ?C' ?D')" 
    using \<open>l = Line (fst l) (snd l)\<close> \<open>m2 = Line (fst m2) (snd m2)\<close> assms(4) by fastforce
  have "?A ?B Par ?C ?D" using Para_Par 
    using IncidentL_def \<open>Para_H (Line (fst l) (snd l)) (Line (fst m1) (snd m1))\<close> 
      \<open>\<not> Col P (fst l) (snd l)\<close> assms(3) isLine_def not_col_distincts by auto
  have "Col P ?C ?D"
    using IncidentL_def assms(3) by auto 
  have "?A ?B Par ?C' ?D'" 
    using IncidentL_def Para_Par \<open>Para_H (Line (fst l) (snd l)) (Line (fst m2) (snd m2))\<close> 
      \<open>(fst l) (snd l) Par (fst m1) (snd m1)\<close> assms(5) 
      isLine_def par_distinct by blast
  have "Col P ?C' ?D'" 
    by (simp add: assms(5) incident_col)
  have "Col ?C' ?C ?D" 
    using \<open>Col P (fst m1) (snd m1)\<close> \<open>Col P (fst m2) (snd m2)\<close> 
      \<open>(fst l) (snd l) Par (fst m1) (snd m1)\<close> 
      \<open>(fst l) (snd l) Par (fst m2) (snd m2)\<close> parallel_uniqueness by blast
  moreover
  have "Col ?D' ?C ?D" 
    using \<open>Col P (fst m1) (snd m1)\<close> \<open>Col P (fst m2) (snd m2)\<close> 
      \<open>(fst l) (snd l) Par (fst m1) (snd m1)\<close> 
      \<open>(fst l) (snd l) Par (fst m2) (snd m2)\<close> parallel_uniqueness by blast
  ultimately show ?thesis
    using tarski_s_euclid_implies_playfair_s_postulate
    by (metis IncidentL_def \<open>(fst l) (snd l) Par (fst m2) (snd m2)\<close> 
        \<open>m2 = Line (fst m2) (snd m2)\<close> assms(3) eq_symmetry incident_eq par_distincts)
qed

subsection "Interpretation"

subsubsection "Neutral dimensionless model"

context Tarski_neutral_dimensionless

begin

interpretation Interpretation_Hilbert_neutral_dimensionless_pre : Hilbert_neutral_dimensionless_pre 
  where IncidL = IncidentL and 
    IncidP = IncidentP and
    EqL = EqTL and 
    EqP = EqTP and 
    IsL = isLine and 
    IsP = isPlane and
    BetH = Between_H and
    CongH = Cong and
    CongaH = CongA_H 
proof -
qed

interpretation Intrepretation_Hilbert_neutral_dimensionless: Hilbert_neutral_dimensionless
  where IncidL = IncidentL and 
    IncidP = IncidentP and
    EqL = EqTL and 
    EqP = EqTP and 
    IsL = isLine and 
    IsP = isPlane and
    BetH = Between_H and
    CongH = Cong and
    CongaH = CongA_H and
    PP = TPA and
    PQ = TPB and
    PR = TPC
proof

(* Begin Preliminaries *)
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col_H A B C" 
  proof -
    {
      fix A B C
      assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        by (simp add: Hilbert_neutral_dimensionless_pre.ColH_def)
      hence "Col_H A B C" 
        using Col_H_def EqTL_def axiom_line_uniqueness cols_coincide_2 
          not_col_distincts by blast
    }
    moreover
    {
      fix A B C
      assume "Col_H A B C" 
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        using Col_H_def by blast
      have "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
        using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l\<close> by blast
    }
    ultimately show ?thesis
      by blast
  qed
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col A B C"
    using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
      cols_coincide by blast

  have 1: "\<forall> A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l
\<longleftrightarrow> same_side_H A B l" 
    by (simp add: Hilbert_neutral_dimensionless_pre.cut_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.same_side_def 
        cut_H_def same_side_H_def)
  have "\<forall> A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
\<longleftrightarrow> same_side'_H A B C D" 
    by (simp add: Hilbert_neutral_dimensionless_pre.same_side'_def 1 same_side'_H_def)

(* End Preliminaries *)

  show "\<And>l. isLine l \<longrightarrow> l =l= l" 
    by (simp add: eq_reflexivity)
  show "\<And>l1 l2. isLine l1 \<and> isLine l2 \<and> l1 =l= l2 \<longrightarrow> l2 =l= l1" 
    using eq_symmetry by blast
  show "\<And>l1 l2 l3. l1 =l= l2 \<and> l2 =l= l3 \<longrightarrow> l1 =l= l3" 
    using eq_transitivity by blast
  show "\<And>p. isPlane p \<longrightarrow> p =p= p" 
    by (simp add: eqp_reflexivity)
  show "\<And>p1 p2. p1 =p= p2 \<longrightarrow> p2 =p= p1" 
    using eqp_symmetry by blast
  show "\<And>p1 p2 p3. p1 =p= p2 \<and> p2 =p= p3 \<longrightarrow> p1 =p= p3" 
    using eqp_transitivity by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l)" 
    using axiom_line_existence by blast
  show "\<And>A B l m.
       A \<noteq> B \<and> isLine l \<and> isLine m \<and>
       IncidentL A l \<and> IncidentL B l \<and> IncidentL A m \<and> IncidentL B m \<longrightarrow>
       l =l= m" 
    using axiom_line_uniqueness by blast
  show "\<forall>l. isLine l \<longrightarrow> (\<exists> A B. IncidentL A l \<and> IncidentL B l \<and> A \<noteq> B)" 
    using axiom_two_points_on_line by blast
  show "TPA \<noteq> TPB \<and> TPB \<noteq> TPC \<and> TPA \<noteq> TPC \<and> 
           \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH TPA TPB TPC" 
    using Bet_cases  between_trivial lower_dim third_point 
      \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close>
    by blast
  show "\<forall>A B C.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
       (\<exists>p. isPlane p \<and> IncidentP A p \<and> IncidentP B p \<and> IncidentP C p)" 
    using bet__coplanar between_trivial2 cop_plane IncidentP_def by blast
  show "\<forall>p. \<exists>A. isPlane p \<longrightarrow> IncidentP A p" 
    by (simp add: axiom_one_point_on_plane)
  show "\<And>A B C p q.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       isPlane p \<and> isPlane q \<and>
       IncidentP A p \<and>
       IncidentP B p \<and>
       IncidentP C p \<and> IncidentP A q \<and> IncidentP B q \<and> IncidentP C q \<longrightarrow>
       p =p= q" 
    using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
      axiom_plane_uniqueness by blast
  show "\<forall>A B l p.
       A \<noteq> B \<and> isLine l \<and> isPlane p \<and>
       IncidentL A l \<and> IncidentL B l \<and> IncidentP A p \<and> IncidentP B p \<longrightarrow>
       Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" 
    by (meson IncidentLP_def Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        axiom_line_on_plane)
  show "\<And>A B C. Between_H A B C \<longrightarrow> A \<noteq> C" 
    using axiom_between_diff by blast
  show "\<And>A B C. Between_H A B C \<longrightarrow> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    by (meson Between_H_def Col_H_def Col_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def cols_coincide_2)
  show "\<And>A B C. Between_H A B C \<longrightarrow> Between_H C B A" 
    using axiom_between_comm by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>C. Between_H A B C)" 
    by (simp add: axiom_between_out)
  show "\<And>A B C. Between_H A B C \<longrightarrow> \<not> Between_H B C A" 
    using axiom_between_only_one by blast
  {
    fix A B C p l
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "isLine l" and
      "IncidentP A p" and
      "IncidentP B p" and
      "IncidentP C p" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" and
      "\<not> IncidentL C l" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B"
    have "\<not> Col A B C" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2)
    moreover have "cut_H l A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.cut_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B\<close> cut_H_def by blast
    ultimately have "cut_H l A C \<or> cut_H l B C" 
      using axiom_pasch Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        \<open>IncidentP A p\<close> \<open>IncidentP B p\<close> \<open>IncidentP C p\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p\<close> \<open>\<not> IncidentL C l\<close> 
        axiom_line_on_plane axiom_two_points_on_line cols_coincide_1 by meson
    hence "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C"  
      by (simp add: Hilbert_neutral_dimensionless_pre.cut_def cut_H_def)
  }
  thus "\<And>A B C p l. \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       isLine l \<and> isPlane p \<and> IncidentP A p \<and> IncidentP B p \<and> IncidentP C p \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p \<and>
       \<not> IncidentL C l \<and> Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B \<longrightarrow>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C" 
    by blast
  {
    fix l 
    fix A B A' P::TPoint
    assume "A \<noteq> B" and
      "A' \<noteq> P" and 
      "isLine l" and
      "IncidentL A' l" and
      "IncidentL P l"
    then obtain B' where "IncidentL B' l \<and> outH A' P B' \<and> Cong A' B' A B"  
      using axiom_hcong_1_existence by presburger
    hence "\<exists>B'. IncidentL B' l \<and> 
               Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.outH_def outH_def by auto
  }
  thus "\<And>l A B A' P::TPoint. A \<noteq> B \<and> A' \<noteq> P \<and> isLine l \<and> IncidentL A' l \<and> IncidentL P l \<longrightarrow>
       (\<exists>B'. IncidentL B' l \<and> 
             Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B)"
    by blast
  show "\<And>A B C D E F. Cong A B C D \<and> Cong A B E F \<longrightarrow> Cong C D E F" 
    using cong_inner_transitivity by blast
  {
    fix A B C A' B' C'
    assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'" and
      "Cong A B A' B'" and
      "Cong B C B' C'" 
    have " (\<exists> l. IncidentL A l \<and> IncidentL B l \<and> IncidentL C l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by force
    then obtain l where "IncidentL A l" and "IncidentL B l" and "IncidentL C l"
      by blast
    hence "Col A B C" 
      by (metis Col_H_def Col_def EqTL_def axiom_line_uniqueness between_trivial cols_coincide_1)
    moreover
    have " (\<exists> l. IncidentL A' l \<and> IncidentL B' l \<and> IncidentL C' l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by force
    then obtain l' where "IncidentL A' l'" and "IncidentL B' l'" and "IncidentL C' l'"
      by blast
    hence "Col A' B' C'" 
      by (metis Col_H_def Col_def EqTL_def axiom_line_uniqueness between_trivial cols_coincide_1)
    moreover
    have "\<not> (\<exists> P. Between_H A P B \<and> Between_H B P C)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C\<close> by blast
    have "\<not> (\<exists> P. Between_H A' P B' \<and> Between_H B' P C')" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'\<close> by blast
    have "Col_H A B C" 
      using calculation(1) cols_coincide_2 by blast
    hence "Bet A B C" 
      using \<open>\<nexists>P. Between_H A P B \<and> Between_H B P C\<close> col_disjoint_bet disjoint_H_def by blast
    moreover
    have "Col_H A' B' C'" 
      by (simp add: calculation(2) cols_coincide_2)
    moreover
    hence "Bet A' B' C'" 
      by (simp add: \<open>\<nexists>P. Between_H A' P B' \<and> Between_H B' P C'\<close> col_disjoint_bet disjoint_H_def)
    ultimately
    have "Cong A C A' C'" 
      using Tarski_neutral_dimensionless.l2_11_b Tarski_neutral_dimensionless_axioms 
        \<open>Cong A B A' B'\<close> \<open>Cong B C B' C'\<close> by fastforce
  }
  thus "\<And>A B C A' B' C'.
       Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C' \<and>
       Cong A B A' B' \<and> Cong B C B' C' \<longrightarrow>
       Cong A C A' C'" 
    by blast
  {
    fix A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
    hence "\<not> Col A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close>
      by blast
    hence "A B C CongA A B C" 
      by (metis conga_refl not_col_distincts)
    hence "CongA_H A B C A B C" 
      by (simp add: CongA_H_def)
  }
  thus "\<And>A B C.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C A B C" 
    by blast
  show "\<And>A B C.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C C B A" 
    using CongA_H_def 
      \<open>\<And>Ca Ba A. \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A Ba Ca 
                 \<longrightarrow> CongA_H A Ba Ca A Ba Ca\<close> conga_right_comm by presburger
  show "\<And>A B C D E F. CongA_H A B C D E F \<longrightarrow> CongA_H C B A F E D" 
    by (meson CongA_H_def axiom_conga_permlr)
  show "\<And>A B C D E F A' C' D' F'.
       CongA_H A B C D E F \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH B A A' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH B C C' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH E D D' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH E F F' \<longrightarrow>
       CongA_H A' B C' D' E F'" 
    using axiom_congaH_outH_congaH CongA_H_def outH_def 
      Interpretation_Hilbert_neutral_dimensionless_pre.outH_def by force
  {
    fix P PO X A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    ultimately
    obtain Y where "A B C CongA X PO Y" and "same_side'_H P Y PO X" 
      using axiom_hcong_4_existence cols_coincide_1 by blast 
    hence "PO \<noteq> X \<and> (\<forall> l. isLine l \<longrightarrow> (IncidentL PO l \<and> IncidentL X l) \<longrightarrow> same_side_H P Y l)"
      using same_side'_H_def by auto
    have "\<exists>Y. CongA_H A B C X PO Y \<and> 
              Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X"
    proof -
      have "CongA_H A B C X PO Y" 
        by (simp add: CongA_H_def \<open>A B C CongA X PO Y\<close>)
      moreover 
      have "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" 
        by (simp add: 
            \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                        = same_side'_H A B C D\<close> \<open>same_side'_H P Y PO X\<close>)
      ultimately show ?thesis
        by blast
    qed
  }
  thus "\<And>P PO X A B C.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
       (\<exists>Y. CongA_H A B C X PO Y \<and>
            Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X)" 
    by blast
  {
    fix P PO X A B C Y Y'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "CongA_H A B C X PO Y" and
      "CongA_H A B C X PO Y'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "A B C CongA X PO Y" 
      using CongA_H_def \<open>CongA_H A B C X PO Y\<close> by blast
    moreover
    have "A B C CongA X PO Y'" 
      using CongA_H_def \<open>CongA_H A B C X PO Y'\<close> by auto
    ultimately
    have "Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
      using \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X\<close> 
        axiom_hcong_4_uniqueness cols_coincide_1 
      by (metis Interpretation_Hilbert_neutral_dimensionless_pre.outH_def 
          \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                      = same_side'_H A B C D\<close> 
          outH_def)
  }
  thus "\<And>P PO X A B C Y Y'.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       CongA_H A B C X PO Y \<and>
       CongA_H A B C X PO Y' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X \<longrightarrow>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
    by blast
  {
    fix A B C A' B' C'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Cong A B A' B'" and
      "Cong A C A' C'" and
      "CongA_H B A C B' A' C'"
    have "\<not> Col_H A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by auto
    moreover
    have "\<not> Col_H A' B' C'" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by blast
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "\<not> Col A' B' C'" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> cols_coincide_2 
      by blast
    moreover
    have "B A C CongA B' A' C'" 
      using CongA_H_def \<open>CongA_H B A C B' A' C'\<close> by auto
    ultimately
    have "CongA_H A B C A' B' C'" 
      using CongA_H_def \<open>Cong A B A' B'\<close> \<open>Cong A C A' C'\<close> l11_49 not_col_distincts by blast
  }
  thus "\<And>A B C A' B' C'.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
       Cong A B A' B' \<and> Cong A C A' C' \<and> CongA_H B A C B' A' C' \<longrightarrow>
       CongA_H A B C A' B' C'" 
    by blast
  show "\<And>A B C D. Cong A B C D \<longrightarrow> Cong A B D C" 
    using not_cong_1243 by blast
  show "\<And>l m P. isLine l \<and> isLine m \<and> IncidentL P l \<and> l =l= m \<longrightarrow> IncidentL P m" 
    using axiom_Incidl_morphism by blast
  show "\<And>p q M. isPlane p \<and> isPlane q \<and> IncidentP M p \<and> p =p= q \<longrightarrow> IncidentP M q" 
    using axiom_Incidp_morphism by blast
  show "\<And>P l. IncidentL P l \<longrightarrow> isLine l" 
    using IncidentL_def by blast
  show "\<And>P p. IncidentP P p \<longrightarrow> isPlane p" 
    using IncidentP_def by blast
qed

end

subsubsection "Neutral 2D model"

context Tarski_2D

begin

interpretation Interpretation_Hilbert_neutral_dimensionless_pre : Hilbert_neutral_dimensionless_pre 
  where IncidL = IncidentL and 
    IncidP = IncidentP and
    EqL = EqTL and 
    EqP = EqTP and 
    IsL = isLine and 
    IsP = isPlane and
    BetH = Between_H and
    CongH = Cong and
    CongaH = CongA_H 
proof -
qed

interpretation Intrepretation_Hilbert_neutral_dimensionless: Hilbert_neutral_dimensionless
  where IncidL = IncidentL and 
    IncidP = IncidentP and
    EqL = EqTL and 
    EqP = EqTP and 
    IsL = isLine and 
    IsP = isPlane and
    BetH = Between_H and
    CongH = Cong and
    CongaH = CongA_H and
    PP = TPA and
    PQ = TPB and
    PR = TPC
proof

(* Begin Preliminaries *)
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col_H A B C" 
  proof -
    {
      fix A B C
      assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        by (simp add: Hilbert_neutral_dimensionless_pre.ColH_def)
      hence "Col_H A B C" 
        using Col_H_def EqTL_def axiom_line_uniqueness cols_coincide_2 not_col_distincts by blast
    }
    moreover
    {
      fix A B C
      assume "Col_H A B C" 
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        using Col_H_def by blast
      have "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
        using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l\<close> by blast
    }
    ultimately show ?thesis
      by blast
  qed
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col A B C"
    using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
      cols_coincide by blast
  have "\<forall> A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l
                 \<longleftrightarrow> same_side_H A B l" 
    by (simp add: Hilbert_neutral_dimensionless_pre.cut_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.same_side_def cut_H_def same_side_H_def)
  have "\<forall> A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                   \<longleftrightarrow> same_side'_H A B C D" 
    by (simp add: Hilbert_neutral_dimensionless_pre.same_side'_def 
        \<open>\<forall>A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l 
                   = same_side_H A B l\<close> 
        same_side'_H_def)

(* End Preliminaries *)

  show "\<And>l. isLine l \<longrightarrow> l =l= l" 
    by (simp add: eq_reflexivity)
  show "\<And>l1 l2. isLine l1 \<and> isLine l2 \<and> l1 =l= l2 \<longrightarrow> l2 =l= l1" 
    using eq_symmetry by blast
  show "\<And>l1 l2 l3. l1 =l= l2 \<and> l2 =l= l3 \<longrightarrow> l1 =l= l3" 
    using eq_transitivity by blast
  show "\<And>p. isPlane p \<longrightarrow> p =p= p" 
    by (simp add: eqp_reflexivity)
  show "\<And>p1 p2. p1 =p= p2 \<longrightarrow> p2 =p= p1" 
    using eqp_symmetry by blast
  show "\<And>p1 p2 p3. p1 =p= p2 \<and> p2 =p= p3 \<longrightarrow> p1 =p= p3" 
    using eqp_transitivity by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l)" 
    using axiom_line_existence by blast
  show "\<And>A B l m.
       A \<noteq> B \<and> isLine l \<and> isLine m \<and>
       IncidentL A l \<and> IncidentL B l \<and> IncidentL A m \<and> IncidentL B m \<longrightarrow>
       l =l= m" 
    using axiom_line_uniqueness by blast
  show "\<forall>l. isLine l \<longrightarrow> (\<exists> A B. IncidentL A l \<and> IncidentL B l \<and> A \<noteq> B)" 
    using axiom_two_points_on_line by blast
  show "TPA \<noteq> TPB \<and> TPB \<noteq> TPC \<and> TPA \<noteq> TPC \<and> 
           \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH TPA TPB TPC" 
    using Bet_cases  between_trivial lower_dim third_point 
      \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close>
    by blast
  show "\<forall>A B C.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
       (\<exists>p. isPlane p \<and> IncidentP A p \<and> IncidentP B p \<and> IncidentP C p)" 
    using bet__coplanar between_trivial2 cop_plane IncidentP_def by blast
  show "\<forall>p. \<exists>A. isPlane p \<longrightarrow> IncidentP A p" 
    by (simp add: axiom_one_point_on_plane)
  show "\<And>A B C p q.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       isPlane p \<and> isPlane q \<and>
       IncidentP A p \<and>
       IncidentP B p \<and>
       IncidentP C p \<and> IncidentP A q \<and> IncidentP B q \<and> IncidentP C q \<longrightarrow>
       p =p= q" 
    using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
      axiom_plane_uniqueness by blast
  show "\<forall>A B l p.
       A \<noteq> B \<and> isLine l \<and> isPlane p \<and>
       IncidentL A l \<and> IncidentL B l \<and> IncidentP A p \<and> IncidentP B p \<longrightarrow>
       Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" 
    by (meson IncidentLP_def Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        axiom_line_on_plane)
  show "\<And>A B C. Between_H A B C \<longrightarrow> A \<noteq> C" 
    using axiom_between_diff by blast
  show "\<And>A B C. Between_H A B C \<longrightarrow> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    by (meson Between_H_def Col_H_def Col_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def cols_coincide_2)
  show "\<And>A B C. Between_H A B C \<longrightarrow> Between_H C B A" 
    using axiom_between_comm by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>C. Between_H A B C)" 
    by (simp add: axiom_between_out)
  show "\<And>A B C. Between_H A B C \<longrightarrow> \<not> Between_H B C A" 
    using axiom_between_only_one by blast
  {
    fix A B C p l
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "isLine l" and
      "IncidentP A p" and
      "IncidentP B p" and
      "IncidentP C p" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" and
      "\<not> IncidentL C l" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B"
    have "\<not> Col A B C" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2)
    moreover have "cut_H l A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.cut_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B\<close> cut_H_def by blast
    ultimately have "cut_H l A C \<or> cut_H l B C" 
      using axiom_pasch Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        \<open>IncidentP A p\<close> \<open>IncidentP B p\<close> \<open>IncidentP C p\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p\<close> \<open>\<not> IncidentL C l\<close> 
        axiom_line_on_plane axiom_two_points_on_line cols_coincide_1 by meson
    hence "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C"  
      by (simp add: Hilbert_neutral_dimensionless_pre.cut_def cut_H_def)
  }
  thus "\<And>A B C p l.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       isLine l \<and> isPlane p \<and> IncidentP A p \<and> IncidentP B p \<and> IncidentP C p \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p \<and>
       \<not> IncidentL C l \<and> Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B \<longrightarrow>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C" 
    by blast
  {
    fix l 
    fix A B A' P::TPoint
    assume "A \<noteq> B" and
      "A' \<noteq> P" and
      "isLine l" and
      "IncidentL A' l" and
      "IncidentL P l"
    then obtain B' where "IncidentL B' l \<and> outH A' P B' \<and> Cong A' B' A B"  
      using axiom_hcong_1_existence by presburger
    hence "\<exists>B'. IncidentL B' l \<and> 
               Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.outH_def outH_def by auto
  }
  thus "\<And>l A B A' P. 
       A \<noteq> B \<and> A' \<noteq> P \<and> isLine l \<and> IncidentL A' l \<and> IncidentL P l \<longrightarrow>
       (\<exists>B'. IncidentL B' l \<and> 
             Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B)"
    by blast
  show "\<And>A B C D E F. Cong A B C D \<and> Cong A B E F \<longrightarrow> Cong C D E F" 
    using cong_inner_transitivity by blast
  {
    fix A B C A' B' C'
    assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'" and
      "Cong A B A' B'" and
      "Cong B C B' C'" 
    have " (\<exists> l. IncidentL A l \<and> IncidentL B l \<and> IncidentL C l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by force
    then obtain l where "IncidentL A l" and "IncidentL B l" and "IncidentL C l"
      by blast
    hence "Col A B C" 
      by (metis Col_H_def Col_def EqTL_def axiom_line_uniqueness between_trivial cols_coincide_1)
    moreover
    have " (\<exists> l. IncidentL A' l \<and> IncidentL B' l \<and> IncidentL C' l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by force
    then obtain l' where "IncidentL A' l'" and "IncidentL B' l'" and "IncidentL C' l'"
      by blast
    hence "Col A' B' C'" 
      by (metis Col_H_def Col_def EqTL_def axiom_line_uniqueness between_trivial cols_coincide_1)
    moreover
    have "\<not> (\<exists> P. Between_H A P B \<and> Between_H B P C)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C\<close> by blast
    have "\<not> (\<exists> P. Between_H A' P B' \<and> Between_H B' P C')" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'\<close> by blast
    have "Col_H A B C" 
      using calculation(1) cols_coincide_2 by blast
    hence "Bet A B C" 
      using \<open>\<nexists>P. Between_H A P B \<and> Between_H B P C\<close> col_disjoint_bet disjoint_H_def by blast
    moreover
    have "Col_H A' B' C'" 
      by (simp add: calculation(2) cols_coincide_2)
    moreover
    hence "Bet A' B' C'" 
      by (simp add: \<open>\<nexists>P. Between_H A' P B' \<and> Between_H B' P C'\<close> col_disjoint_bet disjoint_H_def)
    ultimately
    have "Cong A C A' C'" 
      using Tarski_neutral_dimensionless.l2_11_b Tarski_neutral_dimensionless_axioms 
        \<open>Cong A B A' B'\<close> \<open>Cong B C B' C'\<close> by fastforce
  }
  thus "\<And>A B C A' B' C'.
       Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C' \<and>
       Cong A B A' B' \<and> Cong B C B' C' \<longrightarrow>
       Cong A C A' C'" 
    by blast
  {
    fix A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
    hence "\<not> Col A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close> 
      by blast
    hence "A B C CongA A B C" 
      by (metis conga_refl not_col_distincts)
    hence "CongA_H A B C A B C" 
      by (simp add: CongA_H_def)
  }
  thus "\<And>A B C.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C A B C" 
    by blast
  show "\<And>A B C.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C C B A" 
    using CongA_H_def 
      \<open>\<And>Ca Ba A. \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A Ba Ca 
                 \<longrightarrow> CongA_H A Ba Ca A Ba Ca\<close> conga_right_comm by presburger
  show "\<And>A B C D E F. CongA_H A B C D E F \<longrightarrow> CongA_H C B A F E D" 
    by (meson CongA_H_def axiom_conga_permlr)
  show "\<And>A B C D E F A' C' D' F'.
       CongA_H A B C D E F \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH B A A' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH B C C' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH E D D' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH E F F' \<longrightarrow>
       CongA_H A' B C' D' E F'" 
    using axiom_congaH_outH_congaH CongA_H_def outH_def 
      Interpretation_Hilbert_neutral_dimensionless_pre.outH_def by force
  {
    fix P PO X A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    ultimately
    obtain Y where "A B C CongA X PO Y" and "same_side'_H P Y PO X" 
      using axiom_hcong_4_existence cols_coincide_1 by blast 
    hence "PO \<noteq> X \<and> (\<forall> l. isLine l \<longrightarrow> (IncidentL PO l \<and> IncidentL X l) \<longrightarrow> same_side_H P Y l)"
      using same_side'_H_def by auto
    have "\<exists>Y. CongA_H A B C X PO Y \<and> 
              Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X"
    proof -
      have "CongA_H A B C X PO Y" 
        by (simp add: CongA_H_def \<open>A B C CongA X PO Y\<close>)
      moreover 
      have "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" 
        by (simp add: 
            \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                         = same_side'_H A B C D\<close> \<open>same_side'_H P Y PO X\<close>)
      ultimately show ?thesis
        by blast
    qed
  }
  thus "\<And>P PO X A B C.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
       (\<exists>Y. CongA_H A B C X PO Y \<and>
            Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X)" 
    by blast
  {
    fix P PO X A B C Y Y'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "CongA_H A B C X PO Y" and
      "CongA_H A B C X PO Y'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "A B C CongA X PO Y" 
      using CongA_H_def \<open>CongA_H A B C X PO Y\<close> by blast
    moreover
    have "A B C CongA X PO Y'" 
      using CongA_H_def \<open>CongA_H A B C X PO Y'\<close> by auto
    ultimately
    have "Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
      using \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X\<close> 
        axiom_hcong_4_uniqueness cols_coincide_1 
      by (metis Interpretation_Hilbert_neutral_dimensionless_pre.outH_def 
          \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                      = same_side'_H A B C D\<close> 
          outH_def)
  }
  thus "\<And>P PO X A B C Y Y'.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       CongA_H A B C X PO Y \<and>
       CongA_H A B C X PO Y' \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X \<and>
       Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X \<longrightarrow>
       Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
    by blast
  {
    fix A B C A' B' C'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Cong A B A' B'" and
      "Cong A C A' C'" and
      "CongA_H B A C B' A' C'"
    have "\<not> Col_H A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by auto
    moreover
    have "\<not> Col_H A' B' C'" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by blast
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "\<not> Col A' B' C'" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> cols_coincide_2 by blast
    moreover
    have "B A C CongA B' A' C'" 
      using CongA_H_def \<open>CongA_H B A C B' A' C'\<close> by auto
    ultimately
    have "CongA_H A B C A' B' C'" 
      using CongA_H_def \<open>Cong A B A' B'\<close> \<open>Cong A C A' C'\<close> l11_49 not_col_distincts by blast
  }
  thus "\<And>A B C A' B' C'.
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
       Cong A B A' B' \<and> Cong A C A' C' \<and> CongA_H B A C B' A' C' \<longrightarrow>
       CongA_H A B C A' B' C'" 
    by blast
  show "\<And>A B C D. Cong A B C D \<longrightarrow> Cong A B D C" 
    using not_cong_1243 by blast
  show "\<And>l m P. isLine l \<and> isLine m \<and> IncidentL P l \<and> l =l= m \<longrightarrow> IncidentL P m" 
    using axiom_Incidl_morphism by blast
  show "\<And>p q M. isPlane p \<and> isPlane q \<and> IncidentP M p \<and> p =p= q \<longrightarrow> IncidentP M q" 
    using axiom_Incidp_morphism by blast
  show "\<And>P l. IncidentL P l \<longrightarrow> isLine l" 
    using IncidentL_def by blast
  show "\<And>P p. IncidentP P p \<longrightarrow> isPlane p" 
    using IncidentP_def by blast
qed

interpretation Intrepretation_Hilbert_neutral_2D: Hilbert_neutral_2D
  where IncidL = IncidentL and 
    IncidP = IncidentP and
    EqL = EqTL and 
    EqP = EqTP and 
    IsL = isLine and 
    IsP = isPlane and
    BetH = Between_H and
    CongH = Cong and
    CongaH = CongA_H and
    PP = TPA and
    PQ = TPB and
    PR = TPC
proof
  {
    fix l A B C
    assume "isLine l" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "\<not> IncidentL C l" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B"
    have "\<not> Col A B C" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2)
    have "cut_H l A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.cut_def
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B\<close> cut_H_def by auto
    hence "isLine l \<and> \<not> IncidentL A l \<and> \<not> IncidentL B l \<and> (\<exists> I. IncidentL I l \<and> Between_H A I B)"
      using cut_H_def by blast
    then obtain I where "IncidentL I l" and "Between_H A I B"
      by blast
    hence "Bet A I B \<and> A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C" 
      using Between_H_def \<open>\<not> Col A B C\<close> col_trivial_2 col_trivial_3 by force
    have "Coplanar A B (fst l) (snd l)" 
      using \<open>cut_H l A B\<close> cut_two_sides ncoplanar_perm_16 ts__coplanar by blast
    have "Col I (fst l) (snd l)" 
      using IncidentL_def \<open>IncidentL I l\<close> by auto
    let ?p = "Plane A B C"
    have "isPlane ?p" 
      using EqTP_def \<open>\<not> Col A B C\<close> axiom_plane_existence cols_coincide incidentp_eqp by blast
    moreover have "IncidentP A ?p" 
      using IncidentP_def calculation coplanar_trivial by blast
    moreover have "IncidentP B ?p" 
      using IncidentP_def calculation(1) ncop_distincts by blast
    moreover have "IncidentP C ?p" 
      using IncidentP_def calculation(1) ncop_distincts by blast
    moreover have "IncidentLP l ?p"
    proof -
      have "isLine l" 
        by (simp add: \<open>isLine l\<close>)
      moreover have "isPlane ?p" 
        using \<open>isPlane (Plane A B C)\<close> by blast
      moreover 
      {
        fix AA
        assume "IncidentL AA l" 
        hence "Col AA (fst l) (snd l)" 
          by (simp add: incident_col)
        hence "Coplanar AA A (fst l) (snd l)" 
          using ncop__ncols by blast
        have "Coplanar AA B (fst l) (snd l)" 
          using \<open>Col AA (fst l) (snd l)\<close> ncop__ncols by blast
        have "Coplanar AA I (fst l) (snd l)" 
          using \<open>Col I (fst l) (snd l)\<close> ncop__ncols by blast
        have "isPlane ?p" 
          using \<open>isPlane (Plane A B C)\<close> by blast
        moreover 
        have "Coplanar AA A B C" 
          using all_coplanar by blast
        hence "\<exists> P Q R. ?p = Plane P Q R \<and> Coplanar AA P Q R" 
          by blast
        ultimately have "IncidentP AA ?p"
          using IncidentP_def by blast
      }
      hence "\<forall> A. IncidentL A l \<longrightarrow> IncidentP A ?p" 
        by blast
      ultimately show ?thesis
        using IncidentLP_def by blast
    qed
    moreover have "\<not> IncidentL C l" 
      using \<open>\<not> IncidentL C l\<close> by blast
    ultimately have "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C" 
      by (meson IncidentLP_def Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
          Intrepretation_Hilbert_neutral_dimensionless.pasch 
          \<open>Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B\<close> 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close>)
  }
  thus "\<And>l A B C.
       isLine l \<and>
       \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
       \<not> IncidentL C l \<and> Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B \<longrightarrow>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
       Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C" 
    by blast
qed

end

subsubsection "Neutral 3D model"

context Tarski_3D

begin

interpretation Interpretation_Hilbert_neutral_dimensionless_pre : Hilbert_neutral_dimensionless_pre 
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
proof -
qed

interpretation Intrepretation_Hilbert_neutral_dimensionless: Hilbert_neutral_dimensionless
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
    and PP = TPA           and PQ = TPB           and PR = TPC
proof

(* Begin Preliminaries *)
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col_H A B C" 
  proof -
    {
      fix A B C
      assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        by (simp add: Hilbert_neutral_dimensionless_pre.ColH_def)
      hence "Col_H A B C" 
        using Col_H_def EqTL_def axiom_line_uniqueness cols_coincide_2 not_col_distincts by blast
    }
    moreover
    {
      fix A B C
      assume "Col_H A B C" 
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        using Col_H_def by blast
      have "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
        using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l\<close> by blast
    }
    ultimately show ?thesis
      by blast
  qed
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col A B C"
    using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
      cols_coincide by blast
  have "\<forall> A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l
                  \<longleftrightarrow> same_side_H A B l" 
    by (simp add: Hilbert_neutral_dimensionless_pre.cut_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.same_side_def cut_H_def same_side_H_def)
  have "\<forall> A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                   \<longleftrightarrow> same_side'_H A B C D" 
    by (simp add: Hilbert_neutral_dimensionless_pre.same_side'_def 
        \<open>\<forall>A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l 
                    = same_side_H A B l\<close> 
        same_side'_H_def)

(* End Preliminaries *)

  show "\<And>l. isLine l \<longrightarrow> l =l= l" 
    by (simp add: eq_reflexivity)
  show "\<And>l1 l2. isLine l1 \<and> isLine l2 \<and> l1 =l= l2 \<longrightarrow> l2 =l= l1" 
    using eq_symmetry by blast
  show "\<And>l1 l2 l3. l1 =l= l2 \<and> l2 =l= l3 \<longrightarrow> l1 =l= l3" 
    using eq_transitivity by blast
  show "\<And>p. isPlane p \<longrightarrow> p =p= p" 
    by (simp add: eqp_reflexivity)
  show "\<And>p1 p2. p1 =p= p2 \<longrightarrow> p2 =p= p1" 
    using eqp_symmetry by blast
  show "\<And>p1 p2 p3. p1 =p= p2 \<and> p2 =p= p3 \<longrightarrow> p1 =p= p3" 
    using eqp_transitivity by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l)" 
    using axiom_line_existence by blast
  show "\<And>A B l m.
A \<noteq> B \<and> isLine l \<and> isLine m \<and>
IncidentL A l \<and> IncidentL B l \<and> IncidentL A m \<and> IncidentL B m \<longrightarrow>
l =l= m" 
    using axiom_line_uniqueness by blast
  show "\<forall>l. isLine l \<longrightarrow> (\<exists> A B. IncidentL A l \<and> IncidentL B l \<and> A \<noteq> B)" 
    using axiom_two_points_on_line by blast
  show "TPA \<noteq> TPB \<and> TPB \<noteq> TPC \<and> TPA \<noteq> TPC \<and> 
           \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH TPA TPB TPC" 
    using Bet_cases  between_trivial lower_dim third_point 
      \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close>
    by blast
  show "\<forall>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
  (\<exists>p. isPlane p \<and> IncidentP A p \<and> IncidentP B p \<and> IncidentP C p)" 
    using bet__coplanar between_trivial2 cop_plane IncidentP_def by blast
  show "\<forall>p. \<exists>A. isPlane p \<longrightarrow> IncidentP A p" 
    by (simp add: axiom_one_point_on_plane)
  show "\<And>A B C p q.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  isPlane p \<and> isPlane q \<and>
  IncidentP A p \<and>
  IncidentP B p \<and>
  IncidentP C p \<and> IncidentP A q \<and> IncidentP B q \<and> IncidentP C q \<longrightarrow>
  p =p= q" 
    using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
      axiom_plane_uniqueness by blast
  show "\<forall>A B l p.
  A \<noteq> B \<and> isLine l \<and> isPlane p \<and>
  IncidentL A l \<and> IncidentL B l \<and> IncidentP A p \<and> IncidentP B p \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" 
    by (meson IncidentLP_def Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        axiom_line_on_plane)
  show "\<And>A B C. Between_H A B C \<longrightarrow> A \<noteq> C" 
    using axiom_between_diff by blast
  show "\<And>A B C. Between_H A B C \<longrightarrow> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    by (meson Between_H_def Col_H_def Col_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def cols_coincide_2)
  show "\<And>A B C. Between_H A B C \<longrightarrow> Between_H C B A" 
    using axiom_between_comm by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>C. Between_H A B C)" 
    by (simp add: axiom_between_out)
  show "\<And>A B C. Between_H A B C \<longrightarrow> \<not> Between_H B C A" 
    using axiom_between_only_one by blast
  {
    fix A B C p l
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "isLine l" and
      "IncidentP A p" and
      "IncidentP B p" and
      "IncidentP C p" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" and
      "\<not> IncidentL C l" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B"
    have "\<not> Col A B C" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2)
    moreover have "cut_H l A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.cut_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B\<close> cut_H_def by blast
    ultimately have "cut_H l A C \<or> cut_H l B C" 
      using axiom_pasch Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        \<open>IncidentP A p\<close> \<open>IncidentP B p\<close> \<open>IncidentP C p\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p\<close> \<open>\<not> IncidentL C l\<close> 
        axiom_line_on_plane axiom_two_points_on_line cols_coincide_1 by meson
    hence "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
    Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C"  
      by (simp add: Hilbert_neutral_dimensionless_pre.cut_def cut_H_def)
  }
  thus "\<And>A B C p l.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  isLine l \<and> isPlane p \<and>
  IncidentP A p \<and>
  IncidentP B p \<and>
  IncidentP C p \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p \<and>
  \<not> IncidentL C l \<and> Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
  Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C" 
    by blast
  {
    fix l 
    fix A B A' P::TPoint
    assume "A \<noteq> B" and
      "A' \<noteq> P" and
      "isLine l" and
      "IncidentL A' l" and
      "IncidentL P l"
    then obtain B' where "IncidentL B' l \<and> outH A' P B' \<and> Cong A' B' A B"  
      using axiom_hcong_1_existence by presburger
    hence "\<exists>B'. IncidentL B' l \<and> 
    Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.outH_def outH_def by auto
  }
  thus "\<And>l A B A' P. A \<noteq> B \<and> A' \<noteq> P \<and> isLine l \<and> IncidentL A' l \<and> IncidentL P l \<longrightarrow>
  (\<exists>B'. IncidentL B' l \<and> 
  Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B)"
    by blast
  show "\<And>A B C D E F. Cong A B C D \<and> Cong A B E F \<longrightarrow> Cong C D E F" 
    using cong_inner_transitivity by blast
  {
    fix A B C A' B' C'
    assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'" and
      "Cong A B A' B'" and
      "Cong B C B' C'" 
    have " (\<exists> l. IncidentL A l \<and> IncidentL B l \<and> IncidentL C l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by force
    then obtain l where "IncidentL A l" and "IncidentL B l" and "IncidentL C l"
      by blast
    hence "Col A B C" 
      by (metis Col_H_def Col_def EqTL_def axiom_line_uniqueness between_trivial cols_coincide_1)
    moreover
    have " (\<exists> l. IncidentL A' l \<and> IncidentL B' l \<and> IncidentL C' l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by force
    then obtain l' where "IncidentL A' l'" and "IncidentL B' l'" and "IncidentL C' l'"
      by blast
    hence "Col A' B' C'" 
      by (metis Col_H_def Col_def EqTL_def axiom_line_uniqueness between_trivial cols_coincide_1)
    moreover
    have "\<not> (\<exists> P. Between_H A P B \<and> Between_H B P C)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C\<close> by blast
    have "\<not> (\<exists> P. Between_H A' P B' \<and> Between_H B' P C')" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'\<close> by blast
    have "Col_H A B C" 
      using calculation(1) cols_coincide_2 by blast
    hence "Bet A B C" 
      using \<open>\<nexists>P. Between_H A P B \<and> Between_H B P C\<close> col_disjoint_bet disjoint_H_def by blast
    moreover
    have "Col_H A' B' C'" 
      by (simp add: calculation(2) cols_coincide_2)
    moreover
    hence "Bet A' B' C'" 
      by (simp add: \<open>\<nexists>P. Between_H A' P B' \<and> Between_H B' P C'\<close> col_disjoint_bet disjoint_H_def)
    ultimately
    have "Cong A C A' C'" 
      using Tarski_neutral_dimensionless.l2_11_b Tarski_neutral_dimensionless_axioms 
        \<open>Cong A B A' B'\<close> \<open>Cong B C B' C'\<close> by fastforce
  }
  thus "\<And>A B C A' B' C'.
  Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C' \<and>
  Cong A B A' B' \<and> Cong B C B' C' \<longrightarrow>
  Cong A C A' C'" 
    by blast
  {
    fix A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
    hence "\<not> Col A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close> 
      by blast
    hence "A B C CongA A B C" 
      by (metis Tarski_neutral_dimensionless.conga_refl 
          Tarski_neutral_dimensionless.not_col_distincts Tarski_neutral_dimensionless_axioms)
    hence "CongA_H A B C A B C" 
      by (simp add: CongA_H_def)
  }
  thus "\<And>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C A B C" 
    by blast
  show "\<And>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C C B A" 
    using CongA_H_def 
      \<open>\<And>Ca Ba A. \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A Ba Ca 
                  \<longrightarrow> CongA_H A Ba Ca A Ba Ca\<close> conga_right_comm by presburger
  show "\<And>A B C D E F. CongA_H A B C D E F \<longrightarrow> CongA_H C B A F E D" 
    by (meson CongA_H_def Tarski_neutral_dimensionless.axiom_conga_permlr
        Tarski_neutral_dimensionless_axioms)
  show "\<And>A B C D E F A' C' D' F'. CongA_H A B C D E F \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH B A A' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH B C C' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH E D D' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH E F F' \<longrightarrow>
  CongA_H A' B C' D' E F'" 
    using axiom_congaH_outH_congaH CongA_H_def outH_def 
      Interpretation_Hilbert_neutral_dimensionless_pre.outH_def by force
  {
    fix P PO X A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    ultimately
    obtain Y where "A B C CongA X PO Y" and "same_side'_H P Y PO X" 
      using axiom_hcong_4_existence cols_coincide_1 by blast 
    hence "PO \<noteq> X \<and> (\<forall> l. isLine l \<longrightarrow> (IncidentL PO l \<and> IncidentL X l) \<longrightarrow> same_side_H P Y l)"
      using same_side'_H_def by auto
    have "\<exists>Y. CongA_H A B C X PO Y \<and> 
              Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X"
    proof -
      have "CongA_H A B C X PO Y" 
        by (simp add: CongA_H_def \<open>A B C CongA X PO Y\<close>)
      moreover 
      have "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" 
        by (simp add: 
            \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                        = same_side'_H A B C D\<close> 
            \<open>same_side'_H P Y PO X\<close>)
      ultimately show ?thesis
        by blast
    qed
  }
  thus "\<And>P PO X A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
  (\<exists>Y. CongA_H A B C X PO Y \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X)" 
    by blast
  {
    fix P PO X A B C Y Y'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "CongA_H A B C X PO Y" and
      "CongA_H A B C X PO Y'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "A B C CongA X PO Y" 
      using CongA_H_def \<open>CongA_H A B C X PO Y\<close> by blast
    moreover
    have "A B C CongA X PO Y'" 
      using CongA_H_def \<open>CongA_H A B C X PO Y'\<close> by auto
    ultimately
    have "Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
      using \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X\<close> 
        axiom_hcong_4_uniqueness cols_coincide_1 
      by (metis Interpretation_Hilbert_neutral_dimensionless_pre.outH_def 
          \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                     = same_side'_H A B C D\<close> 
          outH_def)
  }
  thus "\<And>P PO X A B C Y Y'.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  CongA_H A B C X PO Y \<and>
  CongA_H A B C X PO Y' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
    by blast
  {
    fix A B C A' B' C'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Cong A B A' B'" and
      "Cong A C A' C'" and
      "CongA_H B A C B' A' C'"
    have "\<not> Col_H A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by auto
    moreover
    have "\<not> Col_H A' B' C'" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by blast
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "\<not> Col A' B' C'" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> 
        cols_coincide_2 by blast
    moreover
    have "B A C CongA B' A' C'" 
      using CongA_H_def \<open>CongA_H B A C B' A' C'\<close> by auto
    ultimately
    have "CongA_H A B C A' B' C'" 
      using CongA_H_def \<open>Cong A B A' B'\<close> \<open>Cong A C A' C'\<close> l11_49 not_col_distincts by blast
  }
  thus "\<And>A B C A' B' C'.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
  Cong A B A' B' \<and> Cong A C A' C' \<and> CongA_H B A C B' A' C' \<longrightarrow>
  CongA_H A B C A' B' C'" 
    by blast
  show "\<And>A B C D. Cong A B C D \<longrightarrow> Cong A B D C" 
    using not_cong_1243 by blast
  show "\<And>l m P. isLine l \<and> isLine m \<and> IncidentL P l \<and> l =l= m \<longrightarrow> IncidentL P m" 
    using axiom_Incidl_morphism by blast
  show "\<And>p q M. isPlane p \<and> isPlane q \<and> IncidentP M p \<and> p =p= q \<longrightarrow> IncidentP M q" 
    using axiom_Incidp_morphism by blast
  show "\<And>P l. IncidentL P l \<longrightarrow> isLine l" 
    using IncidentL_def by blast
  show "\<And>P p. IncidentP P p \<longrightarrow> isPlane p" 
    using IncidentP_def by blast
qed

interpretation Intrepretation_Hilbert_neutral_3D: Hilbert_neutral_3D
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
    and PP = TPA           and PQ = TPB           and PR = TPC 
    and HS1 = TS1          and HS2 = TS2          and HS3 = TS3 
    and HS4 = TS4
proof
  {
    fix p q A
    assume "isPlane p" and
      "isPlane q" and
      "IncidentP A p" and "IncidentP A q"
    obtain PA PB PC where "p = Plane PA PB PC" and "\<not> Col_H PA PB PC" 
      by (metis Plane_def \<open>isPlane p\<close> cols_coincide_1 isPlane_def surj_pair)
    hence "\<not> Col PA PB PC" 
      by (simp add: cols_coincide)
    obtain QA QB QC where "q = Plane QA QB QC" and "\<not> Col_H QA QB QC" 
      by (metis Plane_def \<open>isPlane q\<close> cols_coincide_1 isPlane_def surj_pair)
    hence "\<not> Col QA QB QC" 
      by (simp add: cols_coincide)
    have "Coplanar A PA PB PC" 
    proof (rule plane_cop [where ?p = "p"])
      show "IncidentP A p" 
        by (simp add: \<open>IncidentP A p\<close>)
      show "IncidentP PA p" 
        using \<open>\<not> Col_H PA PB PC\<close> \<open>p = Plane PA PB PC\<close> axiom_plane_existence 
          eqp_incidentp incidentp_eqp by blast
      show "IncidentP PB p" 
        by (metis IncidentP_def \<open>\<not> Col_H PA PB PC\<close> \<open>isPlane p\<close> \<open>p = Plane PA PB PC\<close>
            axiom_plane_existence plane_cop)
      show "IncidentP PC p" 
        using IncidentP_def \<open>isPlane p\<close> \<open>p = Plane PA PB PC\<close> ncop_distincts by blast
    qed
    have "Coplanar A QA QB QC" 
    proof (rule plane_cop [where ?p = "q"])
      show "IncidentP A q" 
        by (simp add: \<open>IncidentP A q\<close>)
      show "IncidentP QA q" 
        using \<open>\<not> Col_H QA QB QC\<close> \<open>q = Plane QA QB QC\<close> axiom_plane_existence 
          eqp_incidentp incidentp_eqp by blast
      show "IncidentP QB q" 
        by (metis IncidentP_def \<open>\<not> Col_H QA QB QC\<close> \<open>isPlane q\<close> \<open>q = Plane QA QB QC\<close>
            axiom_plane_existence plane_cop)
      show "IncidentP QC q" 
        using IncidentP_def \<open>isPlane q\<close> \<open>q = Plane QA QB QC\<close> ncop_distincts by blast
    qed
    have "plane_intersection_axiom" 
      using upper_dim_3 upper_dim_3_axiom_def upper_dim_3_equivalent_axioms by blast
    have "\<exists> B. Coplanar PA PB PC B \<and> Coplanar QA QB QC B \<and> A \<noteq> B"
    proof -
      have "Coplanar PA PB PC A" 
        by (simp add: \<open>Coplanar A PA PB PC\<close> coplanar_perm_9)
      moreover have "Coplanar QA QB QC A" 
        using \<open>Coplanar A QA QB QC\<close> coplanar_perm_9 by blast
      ultimately show ?thesis
        using \<open>plane_intersection_axiom\<close> plane_intersection_axiom_def by blast
    qed
    hence "\<exists> B. IncidentP B p \<and> IncidentP B q \<and> A \<noteq> B" 
      using IncidentP_def \<open>isPlane p\<close> \<open>isPlane q\<close> \<open>p = Plane PA PB PC\<close> \<open>q = Plane QA QB QC\<close> 
        coplanar_perm_18 by blast
  }
  thus "\<And>p q A. isPlane p \<and> isPlane q \<and> IncidentP A p \<and> IncidentP A q \<longrightarrow> 
  (\<exists>B. IncidentP B p \<and> IncidentP B q \<and> A \<noteq> B)" 
    by blast
  show "\<nexists>p. isPlane p \<and> IncidentP TS1 p \<and> IncidentP TS2 p \<and> IncidentP TS3 p \<and> IncidentP TS4 p" 
    using lower_dim_3' by blast
qed

end

subsubsection "Euclidean model"

context Tarski_Euclidean

begin

interpretation Interpretation_Hilbert_neutral_dimensionless_pre : Hilbert_neutral_dimensionless_pre 
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
proof -
qed

interpretation Intrepretation_Hilbert_neutral_dimensionless: Hilbert_neutral_dimensionless
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
    and PP = TPA           and PQ = TPB           and PR = TPC
proof

(* Begin Preliminaries *)
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col_H A B C" 
  proof -
    {
      fix A B C
      assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        by (simp add: Hilbert_neutral_dimensionless_pre.ColH_def)
      hence "Col_H A B C" 
        using Col_H_def EqTL_def axiom_line_uniqueness cols_coincide_2 not_col_distincts by blast
    }
    moreover
    {
      fix A B C
      assume "Col_H A B C" 
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        using Col_H_def by blast
      have "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
        using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l\<close> by blast
    }
    ultimately show ?thesis
      by blast
  qed
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col A B C"
    using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
      cols_coincide by blast

  have "\<forall> A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l
\<longleftrightarrow> same_side_H A B l" 
    by (simp add: Hilbert_neutral_dimensionless_pre.cut_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.same_side_def cut_H_def same_side_H_def)
  have "\<forall> A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
\<longleftrightarrow> same_side'_H A B C D" 
    by (simp add: Hilbert_neutral_dimensionless_pre.same_side'_def 
        \<open>\<forall>A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l = same_side_H A B l\<close> 
        same_side'_H_def)

(* End Preliminaries *)

  show "\<And>l. isLine l \<longrightarrow> l =l= l" 
    by (simp add: eq_reflexivity)
  show "\<And>l1 l2. isLine l1 \<and> isLine l2 \<and> l1 =l= l2 \<longrightarrow> l2 =l= l1" 
    using eq_symmetry by blast
  show "\<And>l1 l2 l3. l1 =l= l2 \<and> l2 =l= l3 \<longrightarrow> l1 =l= l3" 
    using eq_transitivity by blast
  show "\<And>p. isPlane p \<longrightarrow> p =p= p" 
    by (simp add: eqp_reflexivity)
  show "\<And>p1 p2. p1 =p= p2 \<longrightarrow> p2 =p= p1" 
    using eqp_symmetry by blast
  show "\<And>p1 p2 p3. p1 =p= p2 \<and> p2 =p= p3 \<longrightarrow> p1 =p= p3" 
    using eqp_transitivity by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l)" 
    using axiom_line_existence by blast
  show "\<And>A B l m.
A \<noteq> B \<and> isLine l \<and> isLine m \<and>
IncidentL A l \<and> IncidentL B l \<and> IncidentL A m \<and> IncidentL B m \<longrightarrow>
l =l= m" 
    using axiom_line_uniqueness by blast
  show "\<forall>l. isLine l \<longrightarrow> (\<exists> A B. IncidentL A l \<and> IncidentL B l \<and> A \<noteq> B)" 
    using axiom_two_points_on_line by blast
  show "TPA \<noteq> TPB \<and> TPB \<noteq> TPC \<and> TPA \<noteq> TPC \<and> 
           \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH TPA TPB TPC" 
    using Bet_cases  between_trivial lower_dim third_point 
      \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close>
    by blast
  show "\<forall>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
  (\<exists>p. isPlane p \<and> IncidentP A p \<and> IncidentP B p \<and> IncidentP C p)" 
    using bet__coplanar between_trivial2 cop_plane IncidentP_def by blast
  show "\<forall>p. \<exists>A. isPlane p \<longrightarrow> IncidentP A p" 
    by (simp add: axiom_one_point_on_plane)
  show "\<And>A B C p q.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  isPlane p \<and> isPlane q \<and>
  IncidentP A p \<and>
  IncidentP B p \<and>
  IncidentP C p \<and> IncidentP A q \<and> IncidentP B q \<and> IncidentP C q \<longrightarrow>
  p =p= q" 
    using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
      axiom_plane_uniqueness by blast
  show "\<forall>A B l p.
  A \<noteq> B \<and> isLine l \<and> isPlane p \<and>
  IncidentL A l \<and> IncidentL B l \<and> IncidentP A p \<and> IncidentP B p \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" 
    by (meson IncidentLP_def Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        axiom_line_on_plane)
  show "\<And>A B C. Between_H A B C \<longrightarrow> A \<noteq> C" 
    using axiom_between_diff by blast
  show "\<And>A B C. Between_H A B C \<longrightarrow> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    by (meson Between_H_def Col_H_def Col_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def cols_coincide_2)
  show "\<And>A B C. Between_H A B C \<longrightarrow> Between_H C B A" 
    using axiom_between_comm by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>C. Between_H A B C)" 
    by (simp add: axiom_between_out)
  show "\<And>A B C. Between_H A B C \<longrightarrow> \<not> Between_H B C A" 
    using axiom_between_only_one by blast
  {
    fix A B C p l
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "isLine l" and
      "IncidentP A p" and
      "IncidentP B p" and
      "IncidentP C p" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" and
      "\<not> IncidentL C l" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B"
    have "\<not> Col A B C" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2)
    moreover have "cut_H l A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.cut_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B\<close> cut_H_def by blast
    ultimately have "cut_H l A C \<or> cut_H l B C" 
      using axiom_pasch Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        \<open>IncidentP A p\<close> \<open>IncidentP B p\<close> \<open>IncidentP C p\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p\<close> \<open>\<not> IncidentL C l\<close> 
        axiom_line_on_plane axiom_two_points_on_line cols_coincide_1 by meson
    hence "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
    Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C"  
      by (simp add: Hilbert_neutral_dimensionless_pre.cut_def cut_H_def)
  }
  thus "\<And>A B C p l.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  isLine l \<and> isPlane p \<and>
  IncidentP A p \<and>
  IncidentP B p \<and>
  IncidentP C p \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p \<and>
  \<not> IncidentL C l \<and> Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
  Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C" 
    by blast
  {
    fix l 
    fix A B A' P::TPoint
    assume "A \<noteq> B" and
      "A' \<noteq> P" and
      "isLine l" and
      "IncidentL A' l" and
      "IncidentL P l"
    then obtain B' where "IncidentL B' l \<and> outH A' P B' \<and> Cong A' B' A B"  
      using axiom_hcong_1_existence by presburger
    hence "\<exists>B'. IncidentL B' l \<and> 
    Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.outH_def outH_def by auto
  }
  thus "\<And>l A B A' P. A \<noteq> B \<and> A' \<noteq> P \<and> isLine l \<and> IncidentL A' l \<and> IncidentL P l \<longrightarrow>
  (\<exists>B'. IncidentL B' l \<and> 
  Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B)"
    by blast
  show "\<And>A B C D E F. Cong A B C D \<and> Cong A B E F \<longrightarrow> Cong C D E F" 
    using cong_inner_transitivity by blast
  {
    fix A B C A' B' C'
    assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'" and
      "Cong A B A' B'" and
      "Cong B C B' C'" 
    have " (\<exists> l. IncidentL A l \<and> IncidentL B l \<and> IncidentL C l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by force
    then obtain l where "IncidentL A l" and "IncidentL B l" and "IncidentL C l"
      by blast
    hence "Col A B C" 
      by (metis Col_H_def Col_def EqTL_def axiom_line_uniqueness between_trivial cols_coincide_1)
    moreover
    have " (\<exists> l. IncidentL A' l \<and> IncidentL B' l \<and> IncidentL C' l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by force
    then obtain l' where "IncidentL A' l'" and "IncidentL B' l'" and "IncidentL C' l'"
      by blast
    hence "Col A' B' C'" 
      by (metis Col_H_def Col_def EqTL_def axiom_line_uniqueness between_trivial cols_coincide_1)
    moreover
    have "\<not> (\<exists> P. Between_H A P B \<and> Between_H B P C)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C\<close> by blast
    have "\<not> (\<exists> P. Between_H A' P B' \<and> Between_H B' P C')" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'\<close> by blast
    have "Col_H A B C" 
      using calculation(1) cols_coincide_2 by blast
    hence "Bet A B C" 
      using \<open>\<nexists>P. Between_H A P B \<and> Between_H B P C\<close> col_disjoint_bet disjoint_H_def by blast
    moreover
    have "Col_H A' B' C'" 
      by (simp add: calculation(2) cols_coincide_2)
    moreover
    hence "Bet A' B' C'" 
      by (simp add: \<open>\<nexists>P. Between_H A' P B' \<and> Between_H B' P C'\<close> col_disjoint_bet disjoint_H_def)
    ultimately
    have "Cong A C A' C'" 
      using Tarski_neutral_dimensionless.l2_11_b Tarski_neutral_dimensionless_axioms 
        \<open>Cong A B A' B'\<close> \<open>Cong B C B' C'\<close> by fastforce
  }
  thus "\<And>A B C A' B' C'.
  Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C' \<and>
  Cong A B A' B' \<and> Cong B C B' C' \<longrightarrow>
  Cong A C A' C'" 
    by blast
  {
    fix A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
    hence "\<not> Col A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close> 
      by blast
    hence "A B C CongA A B C" 
      by (metis Tarski_neutral_dimensionless.conga_refl 
          Tarski_neutral_dimensionless.not_col_distincts Tarski_neutral_dimensionless_axioms)
    hence "CongA_H A B C A B C" 
      by (simp add: CongA_H_def)
  }
  thus "\<And>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C A B C" 
    by blast
  show "\<And>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C C B A" 
    using CongA_H_def \<open>\<And>Ca Ba A. \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A Ba Ca 
    \<longrightarrow> CongA_H A Ba Ca A Ba Ca\<close> conga_right_comm by presburger
  show "\<And>A B C D E F. CongA_H A B C D E F \<longrightarrow> CongA_H C B A F E D" 
    by (meson CongA_H_def Tarski_neutral_dimensionless.axiom_conga_permlr
        Tarski_neutral_dimensionless_axioms)
  show "\<And>A B C D E F A' C' D' F'.
  CongA_H A B C D E F \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH B A A' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH B C C' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH E D D' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH E F F' \<longrightarrow>
  CongA_H A' B C' D' E F'" 
    using axiom_congaH_outH_congaH CongA_H_def outH_def 
      Interpretation_Hilbert_neutral_dimensionless_pre.outH_def by force
  {
    fix P PO X A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    ultimately
    obtain Y where "A B C CongA X PO Y" and "same_side'_H P Y PO X" 
      using axiom_hcong_4_existence cols_coincide_1 by blast 
    hence "PO \<noteq> X \<and> (\<forall> l. isLine l \<longrightarrow> (IncidentL PO l \<and> IncidentL X l) \<longrightarrow> same_side_H P Y l)"
      using same_side'_H_def by auto
    have "\<exists>Y. CongA_H A B C X PO Y \<and> 
              Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X"
    proof -
      have "CongA_H A B C X PO Y" 
        by (simp add: CongA_H_def \<open>A B C CongA X PO Y\<close>)
      moreover 
      have "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" 
        by (simp add: 
            \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                        = same_side'_H A B C D\<close> 
            \<open>same_side'_H P Y PO X\<close>)
      ultimately show ?thesis
        by blast
    qed
  }
  thus "\<And>P PO X A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
  (\<exists>Y. CongA_H A B C X PO Y \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X)" 
    by blast
  {
    fix P PO X A B C Y Y'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "CongA_H A B C X PO Y" and
      "CongA_H A B C X PO Y'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "A B C CongA X PO Y" 
      using CongA_H_def \<open>CongA_H A B C X PO Y\<close> by blast
    moreover
    have "A B C CongA X PO Y'" 
      using CongA_H_def \<open>CongA_H A B C X PO Y'\<close> by auto
    ultimately
    have "Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
      using \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X\<close> 
        axiom_hcong_4_uniqueness cols_coincide_1 
      by (metis Interpretation_Hilbert_neutral_dimensionless_pre.outH_def 
          \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                      = same_side'_H A B C D\<close> 
          outH_def)
  }
  thus "\<And>P PO X A B C Y Y'.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  CongA_H A B C X PO Y \<and>
  CongA_H A B C X PO Y' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
    by blast
  {
    fix A B C A' B' C'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Cong A B A' B'" and
      "Cong A C A' C'" and
      "CongA_H B A C B' A' C'"
    have "\<not> Col_H A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by auto
    moreover
    have "\<not> Col_H A' B' C'" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by blast
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "\<not> Col A' B' C'" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> cols_coincide_2 
      by blast
    moreover
    have "B A C CongA B' A' C'" 
      using CongA_H_def \<open>CongA_H B A C B' A' C'\<close> by auto
    ultimately
    have "CongA_H A B C A' B' C'" 
      using CongA_H_def \<open>Cong A B A' B'\<close> \<open>Cong A C A' C'\<close> l11_49 not_col_distincts by blast
  }
  thus "\<And>A B C A' B' C'.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
  Cong A B A' B' \<and> Cong A C A' C' \<and> CongA_H B A C B' A' C' \<longrightarrow>
  CongA_H A B C A' B' C'" 
    by blast
  show "\<And>A B C D. Cong A B C D \<longrightarrow> Cong A B D C" 
    using not_cong_1243 by blast
  show "\<And>l m P. isLine l \<and> isLine m \<and> IncidentL P l \<and> l =l= m \<longrightarrow> IncidentL P m" 
    using axiom_Incidl_morphism by blast
  show "\<And>p q M. isPlane p \<and> isPlane q \<and> IncidentP M p \<and> p =p= q \<longrightarrow> IncidentP M q" 
    using axiom_Incidp_morphism by blast
  show "\<And>P l. IncidentL P l \<longrightarrow> isLine l" 
    using IncidentL_def by blast
  show "\<And>P p. IncidentP P p \<longrightarrow> isPlane p" 
    using IncidentP_def by blast
qed

interpretation Intrepretation_Hilbert_euclidean: Hilbert_euclidean
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
    and PP = TPA           and PQ = TPB           and PR = TPC
proof 
  show "\<forall> l P m1 m2. isLine l \<and> isLine m1 \<and> isLine m2 \<and>
        \<not> IncidentL P l \<and> Interpretation_Hilbert_neutral_dimensionless_pre.Para l m1 \<and>
        IncidentL P m1 \<and> Interpretation_Hilbert_neutral_dimensionless_pre.Para l m2 \<and> 
        IncidentL P m2 \<longrightarrow> m1 =l= m2" 
    using IncidentLP_def Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
      Interpretation_Hilbert_neutral_dimensionless_pre.Para_def 
      Para_H_def axiom_euclid_uniqueness by force
qed

end
end