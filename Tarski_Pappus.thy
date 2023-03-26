(* IsageoCoq2_R1

Version 2.2.0 IsaGeoCoq2_R1, Port part of GeoCoq 3.4.0

Main result:

l13_10: Pappus’ theorem in neutral geometry
l13_14 : forall O A B C O' A' B' C',
  Par_strict O A O' A' -> Col O A B -> Col O B C -> Col O A C ->
  Col O' A' B' -> Col O' B' C' -> Col O' A' C' ->
  Par A C' A' C -> Par B C' B' C -> Par A B' A' B.

@article{braun2017synthetic,
  title={A synthetic proof of Pappus’ theorem in Tarski’s geometry},
  author={Braun, Gabriel and Narboux, Julien},
  journal={Journal of Automated Reasoning},
  volume={58},
  number={2},
  pages={209--230},
  year={2017},
  publisher={Springer}
}

Tarski_Pappus.thy translate (from GeoCoq 3.4.0)

work of Gabriel Braun April 2013:

  [X] Ch13_4_cos.v
  [X] vectors.v
  [X] project.v
  [X] Ch13_5_Pappus_Pascal.v


Copyright (C) 2022-2023 Roland Coghetto roland.coghetto ( a t ) cafr-msa2p.be for Traduction.
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

theory Tarski_Pappus

imports Tarski_Euclidean_2D

begin
  (*>*)

context Tarski_neutral_dimensionless

begin
section "Pappus Pascal"
subsection "Definitions"

subsubsection "Lcos"

(** Definition 13.9. *)

definition Lcos :: "([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow>
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
bool"
  where
    "Lcos lb lc a \<equiv>
  QCong lb \<and> QCong lc \<and> QCongAAcute a \<and>
  (\<exists> A B C. (Per C B A \<and> lb A B \<and> lc A C \<and> a B A C))"

definition EqLcos :: "([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow>
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
bool"
  where
    "EqLcos la a lb b \<equiv> (\<exists> lp. Lcos lp la a \<and> Lcos lp lb b)"

definition Lcos2 :: "([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow>
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
bool"
  where
    "Lcos2 lp l a b \<equiv> \<exists> la. Lcos la l a \<and> Lcos lp la b" 

definition EqLcos2 :: "([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow>
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
bool"
  where
    "EqLcos2 l1 a b l2 c d \<equiv> (\<exists> lp. Lcos2 lp l1 a b \<and> Lcos2 lp l2 c d)" 

definition Lcos3 :: "([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow>
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
bool"
  where
    "Lcos3 lp l a b c \<equiv> \<exists> la lab. Lcos la l a \<and>
Lcos lab la b \<and> Lcos lp lab c"

definition EqLcos3 :: "([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint,TPoint] \<Rightarrow> bool) \<Rightarrow>
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
([TPoint, TPoint, TPoint] \<Rightarrow> bool) \<Rightarrow> 
bool"
  where
    "EqLcos3 l1 a b c l2 d e f \<equiv> (\<exists> lp. Lcos3 lp l1 a b c \<and> Lcos3 lp l2 d e f)" 

subsubsection "Vectors"

(** Vector *)

definition EqV :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  ("_ _ EqV _ _ " [99,99,99,99] 50)
  where
    "A B EqV C D \<equiv> Parallelogram A B D C \<or> (A = B \<and> C = D)"

definition SumV :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  ("_ _ _ _ SumV _ _ " [99,99,99,99,99,99] 50)
  where
    "A B C D SumV E F \<equiv> \<forall> D'. C D EqV B D' \<longrightarrow> A D' EqV E F"

definition SumVExists :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  ("_ _ _ _ SumVExists _ _ " [99,99,99,99,99,99] 50)
  where
    "A B C D SumVExists E F \<equiv> (\<exists> D'. B D' EqV C D \<and> A D' EqV E F)"

definition SameDir :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  ("_ _ SameDir _ _ " [99,99,99,99] 50)
  where
    "A B SameDir C D  \<equiv> 
(A = B \<and> C = D) \<or> (\<exists> D'. C Out D D' \<and> A B EqV C D')" 

definition OppDir :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  ("_ _ OppDir _ _ " [99,99,99,99] 50)
  where
    "A B OppDir C D  \<equiv> A B SameDir D C"

subsubsection "Projections"

definition Proj :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  ("_ _ Proj _ _ _ _" [99,99,99,99,99,99] 50)
  where
    "P Q Proj A B X Y \<equiv>

  A \<noteq> B \<and> X \<noteq> Y \<and> \<not> A B Par X Y \<and> Col A B Q \<and> (P Q Par X Y \<or> P = Q)"

definition CongA3 :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  ("_ _ _ CongA3 _ _ _" [99,99,99,99,99,99] 50)
  where
    "A B C CongA3 A' B' C' \<equiv>
  A B C CongA A' B' C' \<and> B C A CongA B' C' A' \<and> C A B CongA C' A' B'" 

(** Q is the orthogonal projection of P on the line AB. *)
definition Projp :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  ("_ _ Projp _ _" [99,99,99,99] 50)
  where
    "P Q Projp A B \<equiv>
  A \<noteq> B \<and> ((Col A B Q \<and> A B Perp P Q) \<or> (Col A B P \<and> P = Q))"

subsection "Propositions"

subsubsection "Lcos"

(* Gabriel Braun April 2013 *)

lemma l13_6: 
  assumes "Lcos lc l a" and
    "Lcos ld l a"
  shows "lc EqLTarski ld"
proof -
  have H1: "QCong lc \<and> QCong l \<and> QCongAAcute a \<and>
  (\<exists> A B C. (Per C B A \<and> lc A B \<and> l A C \<and> a B A C))" 
    using Lcos_def assms(1) by force
  then obtain X1 Y1 Z1 where "Per Z1 Y1 X1" and "lc X1 Y1" and "l X1 Z1" and "a Y1 X1 Z1"
    by blast
  have H2: "QCong ld \<and> QCong l \<and> QCongAAcute a \<and>
  (\<exists> A B C. (Per C B A \<and> ld A B \<and> l A C \<and> a B A C))" 
    using Lcos_def assms(2) by force
  then obtain X2 Y2 Z2 where "Per Z2 Y2 X2" and "ld X2 Y2" and "l X2 Z2" and "a Y2 X2 Z2"
    by blast
  have "TarskiLen X1 Z1 l" 
    by (simp add: TarskiLen_def H1 \<open>l X1 Z1\<close>)
  have "TarskiLen X2 Z2 l" 
    by (simp add: TarskiLen_def H2 \<open>l X2 Z2\<close>)
  have "Cong X1 Z1 X2 Z2" 
    using \<open>TarskiLen X1 Z1 l\<close> \<open>TarskiLen X2 Z2 l\<close> is_len_cong by auto
  have "Y1 X1 Z1 AngAcute a" 
    using \<open>a Y1 X1 Z1\<close> H1 by (simp add: AngAcute_def)
  have "Y2 X2 Z2 AngAcute a" 
    using H2 by (simp add: AngAcute_def \<open>a Y2 X2 Z2\<close>)
  have "Y1 X1 Z1 CongA Y2 X2 Z2" 
    using \<open>Y1 X1 Z1 AngAcute a\<close> \<open>a Y2 X2 Z2\<close> not_conga_is_anga by blast
  have "TarskiLen X1 Y1 lc" 
    by (simp add: H1 TarskiLen_def \<open>lc X1 Y1\<close>)
  have "TarskiLen X2 Y2 ld" 
    by (simp add: H2 TarskiLen_def \<open>ld X2 Y2\<close>)
  {
    assume "Z1 = Y1"
    hence "X2 Out Y2 Z2" 
      using \<open>Y1 X1 Z1 CongA Y2 X2 Z2\<close> eq_conga_out by blast
    hence "Col Z2 Y2 X2" 
      by (simp add: col_permutation_3 out_col)
    hence "Y2 = Z2 \<or> X2 = Y2" 
      using l8_9 \<open>Per Z2 Y2 X2\<close> by blast
    hence "Y2 = Z2" 
      using \<open>X2 Out Y2 Z2\<close> out_diff1 by blast
    have "TarskiLen X1 Y1 l" 
      using \<open>TarskiLen X1 Z1 l\<close> \<open>Z1 = Y1\<close> by blast
    hence "l EqLTarski lc" 
      by (metis \<open>TarskiLen X1 Y1 lc\<close> all_eql)
    have "TarskiLen X2 Y2 l" 
      by (simp add: \<open>TarskiLen X2 Z2 l\<close> \<open>Y2 = Z2\<close>)
    hence "l EqLTarski ld" 
      by (metis \<open>TarskiLen X2 Y2 ld\<close> all_eql)
    hence ?thesis 
      using EqLTarski_def\<open>l EqLTarski lc\<close> by auto
  }
  moreover
  {
    assume "Z1 \<noteq> Y1"
    {
      assume "Y2 = Z2"
      have "Y2 X2 Y2 CongA Y1 X1 Z1" 
        using \<open>Y1 X1 Z1 CongA Y2 X2 Z2\<close> \<open>Y2 = Z2\<close> conga_sym_equiv by auto
      hence "X1 Out Y1 Z1" 
        by (simp add: eq_conga_out)
      have "Z1 = Y1 \<or> X1 = Y1" 
        using \<open>Per Z1 Y1 X1\<close> \<open>X1 Out Y1 Z1\<close> l8_2 l8_9 out_col by blast
      hence "Y1 = Z1" 
        using \<open>X1 Out Y1 Z1\<close> out_diff1 by blast
      hence False 
        using \<open>Z1 \<noteq> Y1\<close> by blast
    }
    hence "Z2 \<noteq> Y2" 
      by blast
    hence "X1 Y1 Z1 CongA X2 Y2 Z2" 
      by (metis \<open>Per Z1 Y1 X1\<close> \<open>Per Z2 Y2 X2\<close> \<open>Y1 X1 Z1 CongA Y2 X2 Z2\<close> \<open>Z1 \<noteq> Y1\<close> 
          conga_comm conga_diff1 conga_diff45 l11_16)
    {
      assume "Col Z1 X1 Y1"
      hence "X1 = Y1 \<or> Z1 = Y1" 
        using NCol_perm \<open>Per Z1 Y1 X1\<close> l8_3 per_distinct_1 by blast
      hence False 
        using CongA_def \<open>X1 Y1 Z1 CongA X2 Y2 Z2\<close> by blast
    }
    hence "\<not> Col Z1 X1 Y1" 
      by blast
    have "Z1 X1 Y1 CongA Z2 X2 Y2" 
      by (simp add: \<open>Y1 X1 Z1 CongA Y2 X2 Z2\<close> conga_comm)
    have "Cong Z1 Y1 Z2 Y2 \<and> Cong X1 Y1 X2 Y2 \<and> Y1 Z1 X1 CongA Y2 Z2 X2" 
      using l11_50_2 \<open>Cong X1 Z1 X2 Z2\<close> \<open>X1 Y1 Z1 CongA X2 Y2 Z2\<close> 
        \<open>Z1 X1 Y1 CongA Z2 X2 Y2\<close> \<open>\<not> Col Z1 X1 Y1\<close> not_cong_2143 by blast
    hence ?thesis 
      by (metis EqLTarski_def\<open>TarskiLen X1 Y1 lc\<close> \<open>TarskiLen X2 Y2 ld\<close> ex_eql is_len_cong_is_len)
  }
  ultimately show ?thesis
    by blast
qed

lemma null_lcos_eql:
  assumes "Lcos lp l a" and
    "QCongANullAcute a"
  shows "l EqLTarski lp" 
proof -
  have H1:"QCong lp \<and> QCong l \<and> QCongAAcute a \<and>
  (\<exists> A B C. (Per C B A \<and> lp A B \<and> l A C \<and> a B A C))" 
    using assms(1) Lcos_def by blast
  then obtain A B C where "Per C B A" and "lp A B" and "l A C" and "a B A C"
    by blast
  have "A Out B C" 
    using \<open>a B A C\<close> assms(2) is_null_anga_out by force
  hence "Col A B C" 
    by (simp add: out_col)
  hence "C = B \<or> A = B"
    using Per_cases \<open>Per C B A\<close> l8_9 by blast
  moreover have "C = B \<longrightarrow> ?thesis" 
  proof -
    {
      assume "C = B"
      have "QCong l" 
        using H1 by blast
      have "l A B" 
        using \<open>C = B\<close> \<open>l A C\<close> by auto
      hence "TarskiLen A B l" 
        by (simp add: TarskiLen_def \<open>QCong l\<close>)
      moreover have "TarskiLen A B lp" 
        by (simp add: H1 TarskiLen_def \<open>lp A B\<close>)
      ultimately have "l EqLTarski lp" 
        using all_eql assms(1) l13_6 by blast
    }
    thus ?thesis by blast
  qed
  moreover have "A = B \<longrightarrow> ?thesis" 
    using \<open>A Out B C\<close> out_diff1 by blast
  ultimately show ?thesis 
    by fastforce
qed

lemma eql_lcos_null:
  assumes "Lcos l lp a" and 
    "l EqLTarski lp" 
  shows "QCongANullAcute a" 
proof -
  have H1:"QCong l \<and> QCong lp \<and> QCongAAcute a \<and> 
              (\<exists> A B C. (Per C B A \<and> l A B \<and> lp A C \<and> a B A C))" 
    using assms(1) Lcos_def by blast
  then obtain B A C where "Per C A B" and "l B A" and "lp B C" and "a A B C"
    by blast
  have "\<forall> A0 B0. l A0 B0 \<longleftrightarrow> lp A0 B0" 
    using EqLTarski_def assms(2) by force
  have "l B A \<longleftrightarrow> lp B A" 
    using \<open>\<forall>A0 B0. l A0 B0 = lp A0 B0\<close> by auto
  hence "lp B A" 
    by (simp add: \<open>l B A\<close>)
  have "l B C \<longleftrightarrow> lp B C" 
    using \<open>\<forall>A0 B0. l A0 B0 = lp A0 B0\<close> by auto
  hence "l B C" 
    by (simp add: \<open>lp B C\<close>)
  have "Cong B A B C" 
    using Lcos_def TarskiLen_def \<open>l B A\<close> \<open>l B C\<close> assms(1) is_len_cong by force
  obtain B' where "A Midpoint B B'" and "Cong C B C B'" 
    using Per_def \<open>Per C A B\<close> by blast
  have "A \<noteq> B \<and> C \<noteq> B" 
    using anga_distinct H1 \<open>a A B C\<close> by blast
  hence "A \<noteq> B" 
    by simp
  have "C \<noteq> B" 
    using \<open>A \<noteq> B \<and> C \<noteq> B\<close> by fastforce
  have "A = C" 
    by (meson \<open>Cong B A B C\<close> \<open>Per C A B\<close> cong2_per2__cong cong_diff_4 
        cong_pseudo_reflexivity cong_transitivity l8_20_1_R1)
  have "QCongAAcute a" 
    using H1 by blast
  moreover {
    fix A0 B0 C0
    assume "a A0 B0 C0"
    hence "A B A CongA A0 B0 C0" 
      using anga_conga \<open>A = C\<close> \<open>a A B C\<close> calculation by blast
    hence "B0 Out A0 C0" 
      using eq_conga_out by blast
  }
  ultimately show ?thesis 
    using QCongANullAcute_def by auto
qed

lemma lcos_lg_not_null:
  assumes "Lcos l lp a" 
  shows "\<not> QCongNull l \<and> \<not> QCongNull lp"
proof -
  have H1:"QCong l \<and> QCong lp \<and> QCongAAcute a \<and> 
              (\<exists> A B C. (Per C B A \<and> l A B \<and> lp A C \<and> a B A C))" 
    using assms(1) Lcos_def by blast
  then obtain A B C where "Per C B A" and "l A B" and "lp A C" and "a B A C"
    by blast
  hence "B \<noteq> A \<and> C \<noteq> A" 
    using H1 anga_distinct \<open>a B A C\<close> by blast
  {
    assume "QCong l \<and> (\<exists> X. l X X)"
    then obtain X where "l X X" 
      by blast
    hence "Cong A B X X" 
      using \<open>QCong l \<and> (\<exists>X. l X X)\<close> \<open>l A B\<close> lg_cong by blast
    hence False 
      using \<open>B \<noteq> A \<and> C \<noteq> A\<close> cong_identity by blast
  }
  moreover
  {
    assume "QCong lp \<and> (\<exists> X. lp X X)"
    then obtain X where "lp X X" 
      by blast
    hence "Cong A C X X" 
      using \<open>QCong lp \<and> (\<exists>X. lp X X)\<close> \<open>lp A C\<close> lg_cong by blast
    hence False 
      using \<open>B \<noteq> A \<and> C \<noteq> A\<close> cong_diff_2 by blast
  }
  ultimately show ?thesis 
    using QCongNull_def by auto
qed

lemma perp_acute_out: 
  assumes "Acute A B C" and
    "A B Perp C C'" and
    "Col A B C'"
  shows "B Out A C'" 
proof -
  have "B Out C' A" 
    using acute_col_perp__out 
    by (meson acute_sym assms(1) assms(2) assms(3) col_permutation_4 perp_comm perp_right_comm)
  thus ?thesis 
    using l6_6 by blast
qed

lemma perp_col_out__acute_aux: 
  assumes "A B Perp C C'" and
    "B Out A C'"
  shows "Acute A B C" 
  using assms(1) assms(2) perp_out_acute by blast

lemma perp_out__acute: 
  assumes "A B Perp C C'" and
    "Col A B C'" 
  shows "Acute A B C \<longleftrightarrow> B Out A C'" 
  using assms(1) assms(2) perp_acute_out perp_col_out__acute_aux by blast

lemma obtuse_not_acute:
  assumes "Obtuse A B C"
  shows "\<not> Acute A B C" 
  using acute__not_obtuse assms by blast

(* pour compatibilite *)
lemma acute_not_obtuse: 
  assumes "Acute A B C" 
  shows "\<not> Obtuse A B C" 
  using assms obtuse_not_acute by blast

lemma perp_obtuse_bet:
  assumes "A B Perp C C'" and
    "Col A B C'" and
    "Obtuse A B C"
  shows "Bet A B C'" 
proof -
  obtain A0 B0 C0 where "Per A0 B0 C0" and "A0 B0 C0 LtA A B C" 
    using Obtuse_def assms(3) by blast
  have "A0 \<noteq> B0" 
    using \<open>A0 B0 C0 LtA A B C\<close> lta_distincts by auto
  have "C0 \<noteq> B0" 
    using \<open>A0 B0 C0 LtA A B C\<close> lta_distincts by blast
  have "A \<noteq> B" 
    using assms(1) perp_not_eq_1 by blast
  have "C \<noteq> B" 
    using assms(1) assms(2) col_trivial_2 l8_16_1 by blast
  {
    assume "B = C'" 
    hence "Per A B C" 
      using assms(1) perp_left_comm perp_per_1 by blast
    have "A0 B0 C0 CongA A B C" 
      by (simp add: \<open>A \<noteq> B\<close> \<open>A0 \<noteq> B0\<close> \<open>C \<noteq> B\<close> \<open>C0 \<noteq> B0\<close> \<open>Per A B C\<close> \<open>Per A0 B0 C0\<close> l11_16)
    hence False 
      by (simp add: \<open>A0 B0 C0 LtA A B C\<close> lta_not_conga)
  }
  hence "B \<noteq> C'" 
    by blast
  {
    assume "Bet B C' A \<or> Bet C' A B" 
    hence "Bet B A C' \<or> Bet B C' A" 
      using Bet_cases by blast
    hence "B Out A C'" 
      using Out_def \<open>A \<noteq> B\<close> \<open>B \<noteq> C'\<close> by blast
  }
  thus ?thesis using perp_out_acute
    using Col_def assms(1) assms(2) assms(3) obtuse_not_acute by blast
qed

lemma lcos_const0: 
  assumes "Lcos lp l a" and
    "QCongANullAcute a"
  shows "\<exists> A B C. l A B \<and> lp B C \<and> a A B C" 
proof -
  have "QCong lp \<and> QCong l \<and> QCongAAcute a \<and> 
              (\<exists> A B C. (Per C B A \<and> lp A B \<and> l A C \<and> a B A C))" 
    using assms(1) Lcos_def by blast
  thus ?thesis 
    using anga_sym lg_sym by blast
qed

lemma lcos_const1:
  fixes P::TPoint 
  assumes "Lcos lp l a" and 
    "\<not> QCongANullAcute a" 
  shows "\<exists> A B C. \<not> Col A B P \<and> A B OS C P \<and> l A B \<and> lp B C \<and> a A B C" 
proof -
  have H1:"QCong lp \<and> QCong l \<and> QCongAAcute a \<and> 
              (\<exists> A B C. (Per C B A \<and> lp A B \<and> l A C \<and> a B A C))" 
    using assms(1) Lcos_def by blast
  have "\<not> QCongNull lp \<and> \<not> QCongNull l" 
    using assms(1) lcos_lg_not_null by auto
  then obtain A B where "l A B" and "\<not> Col A B P" 
    using H1 ex_points_lg_not_col by blast
  then obtain C' where "a A B C'" and "A B OS C' P" 
    using anga_const_o H1 \<open>\<not> Col A B P\<close> assms(2) by blast
  have "A \<noteq> B \<and> B \<noteq> C'" 
    using \<open>A B OS C' P\<close> os_distincts by blast
  obtain C where "lp B C" and "B Out C C'" 
    using H1 ex_points_lg_not_col \<open>A \<noteq> B \<and> B \<noteq> C'\<close> \<open>\<not> QCongNull lp \<and> \<not> QCongNull l\<close> 
      ex_point_lg_out by blast
  have "A B OS C P" 
    using \<open>A B OS C' P\<close> \<open>B Out C C'\<close> l6_6 not_col_distincts os_out_os by blast
  moreover have "a A B C" 
  proof -
    have "B Out A A"      
      using \<open>A \<noteq> B \<and> B \<noteq> C'\<close> out_trivial by auto
    moreover have "B Out C' C" 
      using Out_cases \<open>B Out C C'\<close> by blast
    ultimately show ?thesis
      using H1 \<open>a A B C'\<close> anga_out_anga by blast
  qed
  ultimately have "\<exists> C. \<not> Col A B P \<and> A B OS C P \<and> l A B \<and> lp B C \<and> a A B C" 
    using \<open>\<not> Col A B P\<close> \<open>l A B\<close> \<open>lp B C\<close> by blast
  thus ?thesis 
    by blast
qed

lemma lcos_const:
  assumes "Lcos lp l a"
  shows "\<exists> A B C. lp A B \<and> l B C \<and> a A B C" 
proof -
  have H1:"QCong lp \<and> QCong l \<and> QCongAAcute a \<and> 
              (\<exists> A B C. (Per C B A \<and> lp A B \<and> l A C \<and> a B A C))" 
    using assms(1) Lcos_def by blast
  then obtain A B C where "Per C B A" and "lp A B" and "l A C" and "a B A C"
    by blast
  hence "lp B A" 
    using lg_sym H1 by blast
  thus ?thesis 
    using \<open>a B A C\<close> \<open>l A C\<close> by auto
qed

lemma lcos_lg_distincts:
  assumes "Lcos lp l a" and
    "l A B" and 
    (*"lp B C" and*)
    "a A B C"
  shows "A \<noteq> B \<and> C \<noteq> B"
proof -
  have H1:"QCong lp \<and> QCong l \<and> QCongAAcute a \<and> 
              (\<exists> A B C. (Per C B A \<and> lp A B \<and> l A C \<and> a B A C))" 
    using assms(1) Lcos_def by blast
  have "\<not> QCongNull lp \<and> \<not> QCongNull l" 
    using assms(1) lcos_lg_not_null by auto
  {
    assume "A = B"
    hence False 
      using H1 \<open>\<not> QCongNull lp \<and> \<not> QCongNull l\<close> assms(2) lg_null_trivial by blast
  }
  moreover
  {
    assume "C = B"
    hence False 
      using H1 anga_distincts assms(3) by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma lcos_const_a:
  assumes "Lcos lp l a"
  shows "\<forall> B. \<exists> A C. l A B \<and> lp B C \<and> a A B C"
proof -
  {
    fix B
    have H1:"QCong lp \<and> QCong l \<and> QCongAAcute a"
      using assms(1) Lcos_def by blast
    then obtain A where "l B A" 
      using ex_point_lg by blast
    hence "l A B" 
      using H1 lg_sym by auto
    have "\<not> QCongNull lp \<and> \<not> QCongNull l" 
      using assms(1) lcos_lg_not_null by auto
    {
      assume "A = B"
      hence "QCongNull l" 
        using H1 \<open>l B A\<close> lg_null_trivial by auto
      hence False 
        using \<open>\<not> QCongNull lp \<and> \<not> QCongNull l\<close> by linarith
    }
    then obtain C' where "a A B C'" 
      using H1 anga_const by blast
    hence "C' \<noteq> B" 
      using \<open>l A B\<close> assms lcos_lg_distincts by auto
    then obtain C where "lp B C" and "B Out C C'" 
      using ex_point_lg_out H1 \<open>\<not> QCongNull lp \<and> \<not> QCongNull l\<close> by metis
    have "a A B C" 
    proof (rule anga_out_anga [where ?A = "A" and ?C = "C'"], simp_all add: H1 \<open>a A B C'\<close>)
      show "B Out A A" 
        using \<open>A = B \<Longrightarrow> False\<close> out_trivial by blast
      show "B Out C' C" 
        using Out_cases \<open>B Out C C'\<close> by auto
    qed
    hence "\<exists> C. l A B \<and> lp B C \<and> a A B C" 
      using \<open>l A B\<close> \<open>lp B C\<close> by blast
    hence "\<exists> A C. l A B \<and> lp B C \<and> a A B C" 
      by blast
  }
  thus ?thesis
    by blast
qed

lemma lcos_const_ab:
  assumes "Lcos lp l a" and
    "l A B"
  shows "\<exists> C. lp B C \<and> a A B C" 
proof -
  have H1:"QCong lp \<and> QCong l \<and> QCongAAcute a"
    using assms(1) Lcos_def by blast
  have "\<not> QCongNull lp \<and> \<not> QCongNull l" 
    using assms(1) lcos_lg_not_null by auto
  {
    assume "A = B"
    hence "QCongNull l" 
      using H1 assms(2) lg_null_trivial by auto
    hence False 
      using \<open>\<not> QCongNull lp \<and> \<not> QCongNull l\<close> by linarith
  }
  then obtain C' where "a A B C'" 
    using H1 anga_const by blast
  hence "C' \<noteq> B" 
    using \<open>l A B\<close> assms lcos_lg_distincts by auto
  then obtain C where "lp B C" and "B Out C C'" 
    using ex_point_lg_out H1 \<open>\<not> QCongNull lp \<and> \<not> QCongNull l\<close> by metis
  have "a A B C" 
  proof (rule anga_out_anga [where ?A = "A" and ?C = "C'"], simp_all add: H1 \<open>a A B C'\<close>)
    show "B Out A A" 
      using \<open>A = B \<Longrightarrow> False\<close> out_trivial by blast
    show "B Out C' C" 
      using Out_cases \<open>B Out C C'\<close> by auto
  qed
  thus ?thesis 
    using \<open>lp B C\<close> by auto
qed

lemma lcos_const_cb:
  assumes "Lcos lp l a" and
    "lp B C"
  shows "\<exists> A. l A B \<and> a A B C" 
proof -
  have H1:"QCong lp \<and> QCong l \<and> QCongAAcute a"
    using assms(1) Lcos_def by blast
  have "\<not> QCongNull lp \<and> \<not> QCongNull l" 
    using assms(1) lcos_lg_not_null by auto
  {
    assume "C = B"
    hence "QCongNull lp" 
      using H1 assms(2) lg_null_trivial by auto
    hence False 
      using \<open>\<not> QCongNull lp \<and> \<not> QCongNull l\<close> by linarith
  }
  then obtain A' where "a C B A'" 
    using H1 anga_const by blast
  hence "A' \<noteq> B" 
    using anga_distinct H1 by blast
  then obtain A where "l B A" and "B Out A A'" 
    using ex_point_lg_out H1 \<open>\<not> QCongNull lp \<and> \<not> QCongNull l\<close> by metis
  have "a A B C" 
  proof (rule anga_out_anga [where ?A = "A'" and ?C = "C"], simp add: H1)
    show "B Out A' A" 
      using \<open>B Out A A'\<close> l6_6 by blast
    show "B Out C C" 
      using \<open>C = B \<Longrightarrow> False\<close> out_trivial by blast
    show "a A' B C" 
      using anga_sym H1 \<open>a C B A'\<close> by blast
  qed
  thus ?thesis 
    using H1 \<open>l B A\<close> lg_sym by blast 
qed

lemma lcos_lg_anga:
  assumes "Lcos lp l a"
  shows "Lcos lp l a \<and> QCong l \<and> QCong lp \<and> QCongAAcute a" 
  using Lcos_def assms by blast

lemma lcos_eql_lcos:
  assumes "lp1 EqLTarski lp2" and
    "l1 EqLTarski l2" and
    "Lcos lp1 l1 a"
  shows "Lcos lp2 l2 a" 
proof -
  have H1:"QCong lp1 \<and> QCong l1 \<and> QCongAAcute a \<and> 
              (\<exists> A B C. (Per C B A \<and> lp1 A B \<and> l1 A C \<and> a B A C))" 
    using assms(3) Lcos_def by blast
  have "QCong l2" 
    using EqLTarski_def H1 QCong_def assms(2) by auto
  moreover have "QCong lp2" 
    using EqLTarski_def H1 QCong_def assms(1) by auto
  ultimately show ?thesis
    using EqLTarski_def H1 Lcos_def assms(1) assms(2) by auto
qed

lemma lcos_not_lg_null:
  assumes "Lcos lp l a"
  shows "\<not> QCongNull lp" 
  using assms lcos_lg_not_null by blast

lemma lcos_const_o: 
  assumes "\<not> Col A B P" and 
    "\<not> QCongANullAcute a" and 
    "QCong l" and
    "QCong lp" and
    "QCongAAcute a" and
    "l A B" and
    "Lcos lp l a"
  shows "\<exists> C. A B OS C P \<and> a A B C \<and> lp B C" 
proof -
  obtain C' where "a A B C'" and "A B OS C' P" 
    using anga_const_o assms(1) assms(2) assms(5) by blast
  hence "C' \<noteq> B" 
    using os_distincts by blast
  have "A \<noteq> B" 
    using assms(1) not_col_distincts by auto
  have "\<not> QCongNull lp" 
    using assms(7) lcos_lg_not_null by blast
  have "B \<noteq> C'" 
    using \<open>C' \<noteq> B\<close> by auto
  obtain lc' where "QCong lc'" and "lc' C' B" 
    using lg_exists by blast
  hence "\<not> QCongNull l \<and> \<not> QCongNull lc'" 
    using \<open>A \<noteq> B\<close> \<open>C' \<noteq> B\<close> assms(3) assms(6) cong_identity lg_cong lg_null_instance by blast
  obtain C where "lp B C" and "B Out C C'"
    using ex_point_lg_out \<open>C' \<noteq> B\<close> \<open>\<not> QCongNull lp\<close> assms(4) by metis
  have "A B OS C P" 
    using Out_cases \<open>A B OS C' P\<close> \<open>B Out C C'\<close> col_trivial_2 os_out_os by blast
  moreover have "a A B C" 
  proof (rule anga_out_anga [where ?A ="A" and ?C="C'"], simp_all add: assms(5) \<open>a A B C'\<close>)
    show "B Out A A" 
      by (simp add: \<open>A \<noteq> B\<close> out_trivial)
    show "B Out C' C" 
      by (simp add: \<open>B Out C C'\<close> l6_6)
  qed
  ultimately show ?thesis
    using \<open>lp B C\<close> by blast
qed

lemma flat_not_acute: 
  assumes "Bet A B C"
  shows "\<not> Acute A B C" 
  using acute_not_bet assms by force

lemma acute_comp_not_acute: 
  assumes "Bet A B C" and
    "Acute A B D"
  shows "\<not> Acute C B D" 
proof -
  {
    assume "Col A C D"
    moreover have "Bet A C D \<longrightarrow> ?thesis" 
      using assms(1) assms(2) between_exchange4 flat_not_acute by blast
    moreover 
    {
      assume "Bet C D A"
      have "Bet A B D \<or> Bet A D B" 
        using \<open>Bet C D A\<close> assms(1) between_symmetry l5_3 by blast
      moreover have "Bet A B D \<longrightarrow> ?thesis"
        using acute_not_bet assms(2) by force
      moreover have "Bet A D B \<longrightarrow> ?thesis" 
        using acute_not_bet acute_sym assms(1) between_exchange3 by blast        
      ultimately have ?thesis 
        by blast
    }
    moreover have "Bet D A C \<longrightarrow> ?thesis" 
      using acute_not_bet acute_sym assms(1) between_exchange2 by blast
    ultimately have ?thesis 
      using Col_def by blast
  }
  moreover
  {
    assume "\<not> Col A C D"
    assume "Acute C B D" 
    obtain A0 B0 C0 where "Per A0 B0 C0" and "A B D LtA A0 B0 C0" 
      using Acute_def assms(2) by blast
    obtain A1 B1 C1 where "Per A1 B1 C1" and "C B D LtA A1 B1 C1" 
      using Acute_def \<open>Acute C B D\<close> by blast
    have "A \<noteq> B" 
      using \<open>A B D LtA A0 B0 C0\<close> lta_distincts by auto
    have "D \<noteq> B" 
      using \<open>A B D LtA A0 B0 C0\<close> lta_distincts by auto
    have "A0 \<noteq> B0" 
      using \<open>A B D LtA A0 B0 C0\<close> lta_distincts by blast
    have "C0 \<noteq> B0" 
      using \<open>A B D LtA A0 B0 C0\<close> lta_distincts by blast
    have "A1 \<noteq> B1"
      using \<open>C B D LtA A1 B1 C1\<close> lta_distincts by auto
    have "C1 \<noteq> B1" 
      using \<open>C B D LtA A1 B1 C1\<close> lta_distincts by blast
    have "A0 B0 C0 CongA A1 B1 C1" 
      by (simp add: \<open>A0 \<noteq> B0\<close> \<open>A1 \<noteq> B1\<close> \<open>C0 \<noteq> B0\<close> \<open>C1 \<noteq> B1\<close> \<open>Per A0 B0 C0\<close> 
          \<open>Per A1 B1 C1\<close> l11_16)
    have "C B D LtA A0 B0 C0" 
      using \<open>A0 \<noteq> B0\<close> \<open>Acute C B D\<close> \<open>C0 \<noteq> B0\<close> \<open>Per A0 B0 C0\<close> acute_per__lta by auto
    have "A \<noteq> C" 
      using \<open>A \<noteq> B\<close> assms(1) between_identity by blast
    have "Col A C B" 
      by (simp add: assms(1) bet_col col_permutation_5)
    obtain P where "A C Perp P B" and "A C OS D P" 
      using \<open>\<not> Col A C D\<close> assms(1) bet_col l10_15 not_col_permutation_5 by blast
    have "A B Perp P B" 
      using \<open>A C Perp P B\<close> \<open>A \<noteq> B\<close> \<open>Col A C B\<close> perp_col by blast
    hence "B PerpAt B A P B" 
      using perp_left_comm perp_perp_in by blast
    hence "Per A B P" 
      by (simp add: perp_in_per_3)
    have "P \<noteq> B" 
      using \<open>B PerpAt B A P B\<close> perp_in_distinct by blast
    have "A B P CongA A0 B0 C0" 
      by (simp add: \<open>A \<noteq> B\<close> \<open>A0 \<noteq> B0\<close> \<open>C0 \<noteq> B0\<close> \<open>P \<noteq> B\<close> \<open>Per A B P\<close> \<open>Per A0 B0 C0\<close> l11_16)
    have "A B D CongA A B D" 
      by (simp add: \<open>A \<noteq> B\<close> \<open>D \<noteq> B\<close> conga_refl)
    moreover have "A0 B0 C0 CongA A B P" 
      using \<open>A B P CongA A0 B0 C0\<close> conga_sym by blast
    ultimately have "A B D LtA A B P" 
      by (simp add: \<open>A B D LtA A0 B0 C0\<close> conga_preserves_lta)
    have "C B D CongA C B D" 
      using \<open>Acute C B D\<close> acute_distincts conga_refl by blast
    hence "C B D LtA A B P" 
      using \<open>A0 B0 C0 CongA A B P\<close> \<open>C B D LtA A0 B0 C0\<close> conga_preserves_lta by auto
    have "A B D LeA A B P \<longleftrightarrow> C B P LeA C B D" 
      by (metis \<open>A \<noteq> B\<close> \<open>Acute C B D\<close> acute_not_bet assms(1) l11_36 not_bet_distincts)
    hence "C B P LeA C B D" 
      by (metis \<open>A B D LtA A B P\<close> \<open>A \<noteq> B\<close> \<open>D \<noteq> B\<close> \<open>P \<noteq> B\<close> lea123456_lta__lta lea_total nlta)
    have "Per C B P" 
      by (meson Col_cases PerpAt_def \<open>B PerpAt B A P B\<close> \<open>Col A C B\<close> col_trivial_1)
    hence "A B P CongA C B P" 
      using \<open>A \<noteq> B\<close> \<open>C B D CongA C B D\<close> \<open>P \<noteq> B\<close> \<open>Per A B P\<close> conga_diff45 l11_16 by blast
    have "C B P CongA A B P" 
      using \<open>A B P CongA C B P\<close> conga_sym_equiv by auto
    hence "A B P LeA C B D" 
      using \<open>C B D CongA C B D\<close> \<open>C B P LeA C B D\<close> l11_30 by blast
    hence False 
      using \<open>C B D LtA A B P\<close> lea__nlta by auto
  }
  ultimately show ?thesis
    by blast
qed

lemma lcos_per: 
  assumes "QCongAAcute a" and
    "QCong l" and 
    "QCong lp" and
    "Lcos lp l a" and
    "l A C" and
    "lp A B" and
    "a B A C"
  shows "Per A B C" 
proof (cases "B = C")
  case True
  thus ?thesis 
    by (simp add: l8_5)
next
  case False
  obtain A0 B0 C0 where "Per C0 B0 A0" and "lp A0 B0" and "l A0 C0" and "a B0 A0 C0" 
    using Lcos_def assms(4) by auto
  hence "B0 A0 C0 CongA B A C" 
    using anga_conga assms(1) assms(7) by blast
  have "Cong A0 C0 A C" 
    using \<open>l A0 C0\<close> assms(2) assms(5) lg_cong by auto
  have "Cong A0 B0 A B" 
    using \<open>lp A0 B0\<close> assms(3) assms(6) lg_cong by auto
  hence "Cong B0 C0 B C \<and> (B0 \<noteq> C0 \<longrightarrow> A0 B0 C0 CongA A B C \<and> A0 C0 B0 CongA A C B)" 
    using \<open>B0 A0 C0 CongA B A C\<close> \<open>Cong A0 C0 A C\<close> l11_49 by blast
  hence "B0 \<noteq> C0" 
    using False cong_reverse_identity by blast
  hence "A0 B0 C0 CongA A B C \<and> A0 C0 B0 CongA A C B" 
    by (simp add: \<open>Cong B0 C0 B C \<and> (B0 \<noteq> C0 \<longrightarrow> A0 B0 C0 CongA A B C \<and> A0 C0 B0 CongA A C B)\<close>)
  thus ?thesis 
    using Per_cases \<open>Per C0 B0 A0\<close> l11_17 by blast
qed

lemma is_null_anga_dec: 
  (*assumes "QCongAAcute a" *)
  shows "QCongANullAcute a \<or> \<not> QCongANullAcute a" 
  by blast

lemma lcos_lg:
  assumes "Lcos lp l a" and
    "A B Perp B C" and
    "a B A C" and
    "l A C"
  shows "lp A B"
proof -
  obtain A' B' C' where "Per C' B' A'" and "lp A' B'" and "l A' C'" and "a B' A' C'" 
    using assms(1) Lcos_def by force
  hence "Cong A C A' C'" 
    by (metis TarskiLen_def assms(1) assms(4) is_len_cong lcos_lg_anga)
  have "B A C CongA B' A' C'" 
    using anga_conga Lcos_def \<open>a B' A' C'\<close> assms(1) assms(3) by blast
  {
    assume "QCongANullAcute a"
    hence "QCongAAcute a \<and> (\<forall> A B C. (a A B C \<longrightarrow> B Out A C))" 
      using QCongANullAcute_def by simp
    hence "\<forall> A B C. a A B C \<longrightarrow> B Out A C" 
      by blast
    have "l EqLTarski lp" 
      using \<open>QCongANullAcute a\<close> assms(1) null_lcos_eql by blast
    have "A Out B C" 
      by (simp add: \<open>\<forall>A B C. a A B C \<longrightarrow> B Out A C\<close> assms(3))
    have "B A Perp C B" 
      by (simp add: assms(2) perp_comm)
    hence "\<not> Col B A C" 
      by (simp add: perp_not_col)
    hence False 
      using \<open>A Out B C\<close> not_col_permutation_4 out_col by blast
    hence ?thesis 
      by blast
  }
  moreover 
  {
    assume "\<not> QCongANullAcute a" 
    have "A \<noteq> B" 
      using assms(2) perp_distinct by presburger
    have "A' \<noteq> B'" 
      using \<open>B A C CongA B' A' C'\<close> conga_diff1 conga_sym_equiv by blast
    have "C \<noteq> B" 
      using assms(2) perp_distinct by blast
    moreover 
    {
      assume "C' = B'" 
      have "QCongAAcute a" 
        using assms(1) Lcos_def by blast
      hence False
        by (metis \<open>A' \<noteq> B'\<close> \<open>C' = B'\<close> \<open>\<not> QCongANullAcute a\<close> \<open>a B' A' C'\<close> 
            bet_out not_bet_distincts out_null_anga)
    }
    hence "C' \<noteq> B'" 
      by blast
    moreover have "B PerpAt A B B C" 
      by (simp add: assms(2) col_trivial_1 col_trivial_3 l8_14_2_1b_bis)
    hence "Per A B C" 
      using perp_in_per by blast
    moreover have "Per A' B' C'" 
      using Per_perm \<open>Per C' B' A'\<close> by blast
    ultimately have "A B C CongA A' B' C'" 
      by (simp add: \<open>A \<noteq> B\<close> \<open>A' \<noteq> B'\<close> l11_16)
    have "Cong C B C' B' \<and> Cong A B A' B' \<and> B C A CongA B' C' A'" 
    proof (rule l11_50_2, simp_all add: \<open>A B C CongA A' B' C'\<close>)
      {
        assume "Col C A B"
        have "B A Perp C B" 
          by (simp add: assms(2) perp_comm)
        hence False 
          using NCol_cases \<open>Col C A B\<close> perp_not_col by blast
      }
      thus "\<not> Col C A B"
        by blast
      show "C A B CongA C' A' B'" 
        by (simp add: \<open>B A C CongA B' A' C'\<close> conga_comm)
      show "Cong C A C' A'" 
        using \<open>Cong A C A' C'\<close> not_cong_2143 by blast
    qed
    have "QCong lp" 
      using Lcos_def assms(1) by blast
    moreover have "lp A' B'" 
      using \<open>lp A' B'\<close> by auto
    moreover have "Cong A' B' A B" 
      using \<open>Cong C B C' B' \<and> Cong A B A' B' \<and> B C A CongA B' C' A'\<close> not_cong_3412 by blast
    ultimately have ?thesis 
      using lg_cong_lg by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma l13_7: 
  assumes "Lcos la l a" and
    "Lcos lb l b" and
    "Lcos lab la b" and
    "Lcos lba lb a"
  shows "lab EqLTarski lba" 
proof -
  have "QCong l" 
    using assms(1) lcos_lg_anga by blast
  have "QCong la" 
    using assms(1) lcos_lg_anga by blast
  have "QCongAAcute a" 
    using assms(4) lcos_lg_anga by blast
  have "QCong lb" 
    using assms(2) lcos_lg_anga by blast
  have "QCongAAcute b" 
    using assms(2) lcos_lg_anga by blast
  have "QCong lab" 
    using assms(3) lcos_lg_anga by blast
  have "QCong lba" 
    using assms(4) lcos_lg_anga by blast
  {
    assume "QCongANullAcute a"
    hence "lb EqLTarski lba" 
      using assms(4) null_lcos_eql by blast
    have "l EqLTarski la" 
      using \<open>QCongANullAcute a\<close> assms(1) null_lcos_eql by auto
    have "Lcos lab l b" 
      using EqLTarski_def\<open>l EqLTarski la\<close> assms(3) by presburger
    have "lb EqLTarski lab" 
      using \<open>Lcos lab l b\<close> assms(2) l13_6 by auto
    hence ?thesis 
      by (meson \<open>l EqLTarski la\<close> \<open>lb EqLTarski lba\<close> assms(2) l13_6 lcos_eql_lcos)
  }
  moreover 
  {
    assume "\<not> QCongANullAcute a"
    have "QCongANullAcute b \<longrightarrow> ?thesis" 
      by (meson assms(1) assms(2) assms(3) assms(4) l13_6 lcos_eql_lcos null_lcos_eql)
    moreover {
      assume "\<not> QCongANullAcute b"
      obtain C A B where "la C A" and "l A B" and "a C A B" 
        using assms(1) lcos_const by blast
      have "C \<noteq> A \<and> B \<noteq> A" 
        by (metis \<open>l A B\<close> \<open>la C A\<close> assms(1) assms(3) lcos_const_ab lcos_lg_distincts)
      {
        assume "Col A B C"
        hence "Col C A B" 
          using Col_cases by blast
        hence "A Out C B \<and> QCongANullAcute a" 
          using anga_col_null \<open>QCongAACute a\<close> \<open>a C A B\<close> by blast
        hence False 
          using \<open>\<not> QCongANullAcute a\<close> by blast
      }
      obtain P where "P C Reflect B A" 
        using l10_2_existence by blast
      hence "C P Reflect B A" 
        using l10_4 by blast
      moreover have "\<not> Col B A C" 
        using \<open>Col A B C \<Longrightarrow> False\<close> col_permutation_4 by blast
      ultimately have "\<not> Col B A P" 
        using osym_not_col by blast
      have "l B A" 
        by (simp add: \<open>QCong l\<close> \<open>l A B\<close> lg_sym)
      have "\<exists> D. B A OS D P \<and> b B A D \<and> lb A D" 
        using lcos_const_o [where ?l = "l"] \<open>\<not> Col B A P\<close> \<open>\<not> QCongANullAcute b\<close>
          \<open>QCong l\<close> \<open>QCong lb\<close> \<open>QCongAACute b\<close> \<open>l B A\<close> assms(2) by simp
      then obtain D where "B A OS D P" and "b B A D" and "lb A D" 
        by blast
      have "P \<noteq> C" 
        using Col_cases \<open>C P Reflect B A\<close> \<open>Col A B C \<Longrightarrow> False\<close> l10_8 by blast
      hence "B A TS P C" 
        using l10_14 \<open>C \<noteq> A \<and> B \<noteq> A\<close> \<open>P C Reflect B A\<close> by simp
      have "B A OS P D" 
        by (simp add: \<open>B A OS D P\<close> one_side_symmetry)
      hence "B A TS D C" 
        using l9_8_2 [where ?A = "P"] \<open>B A TS P C\<close> by blast
      have "la A C" 
        by (simp add: \<open>QCong la\<close> \<open>la C A\<close> lg_sym)
      hence "Per A C B" 
        using lcos_per \<open>QCong l\<close> \<open>QCong la\<close> \<open>QCongAACute a\<close> \<open>a C A B\<close> \<open>l A B\<close> 
          assms(1) by blast
      have "b D A B" 
        using anga_sym \<open>QCongAACute b\<close> \<open>b B A D\<close> by auto
      hence "Per A D B"  using lcos_per 
        using \<open>QCong l\<close> \<open>QCong lb\<close> \<open>QCongAACute b\<close> \<open>l A B\<close> \<open>lb A D\<close> assms(2) by blast
      {
        assume "Col C D A"
        hence "Per B C D" 
          using \<open>B A TS D C\<close> \<open>Per A C B\<close> \<open>Per A D B\<close> col_permutation_3 
            per2_preserves_diff ts_distincts by blast
        have "Per B D C" 
          using \<open>B A TS D C\<close> \<open>Col C D A\<close> \<open>Per A C B\<close> \<open>Per A D B\<close> not_col_permutation_1 
            per2_preserves_diff ts_distincts by blast
        have "C = D" 
          using \<open>Per B C D\<close> \<open>Per B D C\<close> l8_7 by blast
        then obtain T where "Col T B A" and "Bet C T C" 
          using \<open>B A TS D C\<close> ts_distincts by blast
        hence "C = T" 
          using between_identity by blast
        hence False 
          using \<open>B A TS D C\<close> \<open>C = D\<close> ts_distincts by blast
      }
      obtain E where "Col C D E" and "C D Perp A E" 
        using \<open>Col C D A \<Longrightarrow> False\<close> l8_18_existence by blast
      have "B A C CongA D A E \<and> B A D CongA C A E \<and> Bet C E D" 
      proof (rule l13_2, simp_all add: \<open>Col C D E\<close>)
        show "A B TS C D" 
          using \<open>B A TS D C\<close> invert_two_sides l9_2 by blast
        show "Per B C A" 
          using Per_perm \<open>Per A C B\<close> by blast
        show "Per B D A" 
          using Per_cases \<open>Per A D B\<close> by blast
        show "A E Perp C D" 
          using Perp_perm \<open>C D Perp A E\<close> by blast
      qed
      hence "a D A E" 
        using anga_conga_anga \<open>QCongAACute a\<close> \<open>a C A B\<close> conga_left_comm by blast
      have "b C A E" 
        using anga_conga_anga \<open>B A C CongA D A E \<and> B A D CongA C A E \<and> Bet C E D\<close> 
          \<open>QCongAACute b\<close> \<open>b B A D\<close> by blast
      have "C E Perp A E"
      proof (rule perp_col [where ?B = "D"])
        {
          assume "C = E"
          {
            fix A0 B0 C0
            assume "b A0 B0 C0"
            hence "A0 B0 C0 CongA C A C" 
              using anga_conga \<open>C = E\<close> \<open>QCongAACute b\<close> \<open>b C A E\<close> by blast
            have "A Out C C" 
              by (simp add: \<open>C \<noteq> A \<and> B \<noteq> A\<close> out_trivial)
            hence "B0 Out A0 C0" 
              using l11_21_a \<open>A0 B0 C0 CongA C A C\<close> conga_sym_equiv by blast
          }
          hence "QCongANullAcute b" 
            using  \<open>QCongAACute b\<close> QCongANullAcute_def by blast
        }
        thus "C \<noteq> E" 
          using \<open>\<not> QCongANullAcute b\<close> by blast
        show "C D Perp A E" 
          by (simp add: \<open>C D Perp A E\<close>)
        show "Col C D E"
          by (simp add: \<open>Col C D E\<close>)
      qed
      have "lab A E" 
      proof (rule lcos_lg [where ?l = "la" and ?a = "b" and ?C = "C"])
        show " Lcos lab la b" 
          by (simp add: assms(3))
        show "A E Perp E C" 
          using Perp_perm \<open>C E Perp A E\<close> by blast
        show "b E A C" using anga_sym 
          using \<open>QCongAACute b\<close> \<open>b C A E\<close> by auto
        show "la A C" 
          using lg_sym by (simp add: \<open>la A C\<close>)
      qed
      have "D E Perp A E" 
      proof (rule perp_col [where ?B = "C"]) 
        {
          assume "D = E"
          {
            fix A0 B0 C0
            assume "a A0 B0 C0"
            have "A0 B0 C0 CongA D A D" 
              using anga_conga \<open>D = E\<close> \<open>a A0 B0 C0\<close> \<open>a D A E\<close> \<open>QCongAACute a\<close> by blast
            have "B0 Out A0 C0" 
            proof (rule l11_21_a [where ?A="D" and ?B="A" and ?C="D"])
              show "A Out D D" 
                using \<open>Col C D A \<Longrightarrow> False\<close> \<open>Col C D E\<close> \<open>D = E\<close> out_trivial by force
              show "D A D CongA A0 B0 C0" 
                by (simp add: \<open>A0 B0 C0 CongA D A D\<close> conga_sym)
            qed
          }
          hence "QCongANullAcute a" 
            using \<open>QCongAACute a\<close> QCongANullAcute_def by blast
          hence False 
            using \<open>\<not> QCongANullAcute a\<close> by blast
        }
        thus "D \<noteq> E" 
          by blast
        show "D C Perp A E" 
          using Perp_cases \<open>C D Perp A E\<close> by blast
        show "Col D C E"
          using \<open>Col C D E\<close> not_col_permutation_4 by blast
      qed
      have "lba A E" 
      proof (rule lcos_lg [where ?a="a" and ?l = "lb" and ?C="D"], 
          simp_all add: assms(4) \<open>lb A D\<close>)
        show "A E Perp E D" 
          using Perp_cases \<open>D E Perp A E\<close> by blast
        show "a E A D" 
          using \<open>a D A E\<close> anga_sym \<open>QCongAACute a\<close> by blast
      qed
      hence "lab EqLTarski lba"  
        using \<open>QCong lab\<close> \<open>QCong lba\<close> \<open>lab A E\<close> assms(3) ex_eqL l13_6 by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma out_acute: 
  assumes "B Out A C" 
  shows "Acute A B C" 
proof -
  have "A \<noteq> B \<and> C \<noteq> B" 
    using assms out_distinct by auto
  then obtain Q where "\<not> Col A B Q" 
    using not_col_exists by blast
  then obtain P where "A B Perp P B" and "A B OS Q P"
    using l10_15 not_col_distincts by blast
  hence "Per P B A" 
    using Perp_perm perp_per_1 by blast
  hence "Per A B P" 
    using l8_2 by blast
  moreover have "A B C LtA A B P" 
  proof -
    have "A B C LeA A B P" 
      using \<open>A B Perp P B\<close> \<open>A \<noteq> B \<and> C \<noteq> B\<close> assms l11_31_1 perp_not_eq_2 by auto
    moreover have "\<not> A B C CongA A B P" 
      by (metis Col_def Out_def \<open>A B OS Q P\<close> \<open>Per P B A\<close> assms col124__nos l11_21_a 
          l8_20_1_R1 l8_6)
    ultimately show ?thesis 
      using LtA_def by blast
  qed
  ultimately show ?thesis 
    using Acute_def by blast
qed

lemma perp_acute: 
  assumes "Col A C P" and
    "P PerpAt B P A C" 
  shows "Acute A B P" 
proof (cases "Col P A B")
  case True
  thus ?thesis 
    by (metis acute_trivial assms(2) l8_14_2_1b not_col_distincts 
        not_col_permutation_2 perp_in_distinct)
next
  case False
  have "Per A P B" 
    using PerpAt_def assms(2) col_trivial_1 l8_2 by presburger
  thus ?thesis using l11_43 
    by (metis False acute_sym col_trivial_1 col_trivial_3)
qed

lemma null_lcos: 
  assumes "QCong l" and 
    "\<not> QCongNull l" and
    "QCongANullAcute a"
  shows "Lcos l l a" 
proof -
  obtain A B C where "a A B C" 
    using ex_points_anga QCongANullAcute_def assms(3) by presburger
  hence "B Out A C" 
    using assms(3) is_null_anga_out by auto
  hence "A \<noteq> B" 
    by (simp add: out_distinct)
  obtain A' B' where "l A' B'" 
    using assms(1) ex_points_lg by blast
  obtain P where "l B P" and "B Out P A" 
    using ex_point_lg_out \<open>A \<noteq> B\<close> assms(1) assms(2) by metis
  moreover have "Per P P B" 
    by (simp add: l8_20_1_R1)
  moreover have "a P B P" 
    by (metis assms(1) assms(2) assms(3) calculation(1) is_null_all lg_null_trivial)
  ultimately show ?thesis 
    using Lcos_def QCongANullAcute_def assms(1) assms(3) by auto
qed

lemma lcos_exists:
  assumes "QCongAAcute a" and
    "QCong l" and
    "\<not> QCongNull l"
  shows "\<exists> lp. Lcos lp l a" 
proof (cases "QCongANullAcute a")
  case True
  thus ?thesis 
    using assms(2) assms(3) null_lcos by blast
next
  case False
  obtain A B where "l A B" 
    using assms(2) ex_points_lg by presburger
  obtain C where "a A B C" 
    by (metis QCongNull_def \<open>l A B\<close> anga_const assms(1) assms(2) assms(3))
  {
    assume "Col B C A"
    hence "B Out A C \<and> QCongANullAcute a" 
      using \<open>a A B C\<close> anga_col_out assms(1) col_permutation_2 out_null_anga by blast
    hence False 
      using False by blast
  }
  hence "\<not> Col B C A" 
    by blast
  then obtain P where "Col B C P" and "B C Perp A P" 
    using l8_18_existence by blast
  obtain lp where "QCong lp" and "lp B P" 
    using lg_exists by fastforce
  obtain A' B' C' where "Acute A' B' C'" and "\<forall> X Y Z. A' B' C' CongA X Y Z \<longleftrightarrow> a X Y Z"
    using QCongAAcute_def assms(1) by metis
  hence "A' B' C' CongA A B C" 
    using \<open>a A B C\<close> by auto
  hence "A B C CongA A' B' C'" 
    using not_conga_sym by blast
  moreover have "C' InAngle A' B' C'" 
    using \<open>Acute A' B' C'\<close> acute_distincts inangle3123 by blast
  ultimately have "A B C LeA A' B' C'" 
    by (simp add: conga__lea)
  hence "Acute A B C" 
    using \<open>Acute A' B' C'\<close> acute_lea_acute by blast
  have "B P Perp P A" 
  proof (rule perp_col [where ?B = "C"], simp_all add:\<open>Col B C P\<close>)
    {
      assume "B = P"
      hence "Per A B C" 
        using \<open>B C Perp A P\<close> l8_2 perp_per_1 by blast
      moreover have "\<not> Per A B C" 
        using \<open>Acute A B C\<close> by (simp add: acute_not_per)
      ultimately have False 
        by simp
    }
    thus "B \<noteq> P" 
      by blast
    show "B C Perp P A" 
      using Perp_perm \<open>B C Perp A P\<close> by blast
  qed
  hence "Per A P B" 
    using Perp_cases perp_per_1 by blast
  moreover have "lp B P" 
    using \<open>lp B P\<close> by blast
  moreover have "l B A" 
    by (simp add: \<open>l A B\<close> assms(2) lg_sym)
  moreover have "a A B P" 
  proof (rule anga_out_anga [where ?A="A" and ?C="C"], simp_all add:\<open>a A B C\<close>)
    show "QCongAACute a" 
      by (simp add: assms(1))
    show "B Out A A" 
      by (metis \<open>\<not> Col B C A\<close> col_trivial_3 out_trivial)
    show "B Out C P"
    proof (rule perp_acute_out [where ?C="A"])
      show "Acute C B A" 
        by (simp add: \<open>Acute A B C\<close> acute_sym)
      show "C B Perp A P" 
        using Perp_perm \<open>B C Perp A P\<close> by blast
      show "Col C B P" 
        using \<open>Col B C P\<close> not_col_permutation_4 by blast
    qed
  qed
  hence "a P B A" 
    using anga_sym assms(1) by blast
  ultimately show ?thesis 
    using Lcos_def \<open>\<And>thesis. (\<And>lp. \<lbrakk>QCong lp; lp B P\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
      assms(1) assms(2) by fastforce
qed

lemma lcos_uniqueness: 
  assumes "Lcos l1 l a" and
    "Lcos l2 l a"
  shows "l1 EqLTarski l2" 
  using assms(1) assms(2) l13_6 by blast

lemma lcos_eqa_lcos: 
  assumes "Lcos lp l a" and
    "a EqA b"
  shows "Lcos lp l b"
proof -
  have "Lcos lp l a" 
    using lcos_lg_anga assms(1) by blast
  have "QCong l" 
    using lcos_lg_anga assms(1) by blast
  have "QCong lp" 
    using lcos_lg_anga assms(1) by blast
  have "QCongAAcute a" 
    using lcos_lg_anga assms(1) by blast
  have "\<forall> A B C. a A B C \<longleftrightarrow> b A B C" 
    using EqA_def assms(2) by presburger
  have "QCongA a" using anga_is_ang 
    by (simp add: \<open>QCongAACute a\<close>)
  have "QCongA b" 
    using eqA_preserves_ang \<open>QCongA a\<close> assms(2) by blast
  have "QCongAAcute b" 
    using eqA_preserves_anga \<open>QCongAACute a\<close> assms(2) by blast
  obtain A B C where "Per C B A" and "lp A B" and "l A C" and "a B A C" 
    using Lcos_def assms(1) by auto
  thus ?thesis 
    using \<open>\<forall>A B C. a A B C = b A B C\<close> assms(1) by presburger
qed

lemma lcos_eq_refl:
  assumes "QCong la" and
    "\<not> QCongNull la" and
    "QCongAAcute a"
  shows "EqLcos la a la a"
proof -
  obtain lp where "Lcos lp la a" 
    using lcos_exists assms(1) assms(2) assms(3) by blast
  thus ?thesis
    using EqLcos_def by blast
qed

lemma lcos_eq_sym:
  assumes "EqLcos la a lb b"
  shows "EqLcos lb b la a" 
proof -
  obtain lp where "Lcos lp la a" and "Lcos lp lb b" 
    using EqLcos_def assms(1) by blast
  thus ?thesis
    using EqLcos_def by blast
qed

lemma lcos_eq_trans:
  assumes "EqLcos la a lb b" and
    "EqLcos lb b lc c"
  shows "EqLcos la a lc c" 
proof -
  obtain lab where "Lcos lab la a" and "Lcos lab lb b" 
    using EqLcos_def assms(1) by blast
  obtain lbc where "Lcos lbc lb b" and "Lcos lbc lc c" 
    using EqLcos_def assms(2) by blast
  hence "lab EqLTarski lbc" 
    using \<open>Lcos lab lb b\<close> lcos_uniqueness by auto
  hence "Lcos lbc la a" 
    by (metis EqLTarski_def \<open>Lcos lab la a\<close> lcos_eql_lcos)
  thus ?thesis 
    using EqLcos_def \<open>Lcos lbc lc c\<close> by blast
qed

lemma lcos2_comm:
  assumes "Lcos2 lp l a b"
  shows "Lcos2 lp l b a" 
proof -
  obtain la where "Lcos la l a" and "Lcos lp la b" 
    using Lcos2_def assms(1) by blast
  hence "\<not> QCongNull la \<and> \<not> QCongNull l" 
    using lcos_lg_not_null by blast
  then obtain lb where "Lcos lb l b" 
    using lcos_exists \<open>Lcos la l a\<close> \<open>Lcos lp la b\<close> lcos_lg_anga by blast
  moreover 
  obtain lp' where "Lcos lp' lb a" 
    by (meson \<open>Lcos la l a\<close> calculation lcos_exists lcos_lg_anga lcos_not_lg_null)
  hence "Lcos lp lb a"     
    by (meson \<open>Lcos la l a\<close> \<open>Lcos lp la b\<close> calculation l13_6 l13_7 lcos_eql_lcos)
  ultimately show ?thesis
    using Lcos2_def by blast
qed

lemma lcos2_exists:
  assumes "QCong l" and
    "\<not> QCongNull l" and
    "QCongAAcute a" and
    "QCongAAcute b" 
  shows "\<exists> lp. Lcos2 lp l a b" 
proof -
  obtain la where "Lcos la l a" 
    using assms(1) assms(2) assms(3) lcos_exists by blast
  hence "\<not> QCongNull la \<and> \<not> QCongNull l" 
    using lcos_lg_not_null by blast
  then obtain lab where "Lcos lab la b" 
    using \<open>Lcos la l a\<close> assms(4) lcos_exists lcos_lg_anga by blast
  thus ?thesis 
    using Lcos2_def \<open>Lcos la l a\<close> by blast
qed

lemma lcos2_exists': 
  assumes "QCong l" and
    "\<not> QCongNull l" and
    "QCongAAcute a" and
    "QCongAAcute b"
  shows "\<exists> la lab. Lcos la l a \<and> Lcos lab la b" 
proof -
  obtain la where "Lcos la l a" 
    using assms(1) assms(2) assms(3) lcos_exists by blast
  hence "\<not> QCongNull la \<and> \<not> QCongNull l" 
    using lcos_lg_not_null by blast
  then obtain lab where "Lcos lab la b" 
    using \<open>Lcos la l a\<close> assms(4) lcos_exists lcos_lg_anga by blast
  thus ?thesis 
    using \<open>Lcos la l a\<close> by blast
qed

lemma lcos2_eq_refl: 
  assumes "QCong l" and
    "\<not> QCongNull l" and
    "QCongAAcute a" and
    "QCongAAcute b" 
  shows "EqLcos2 l a b l a b" 
  by (simp add: EqLcos2_def assms(1) assms(2) assms(3) assms(4) lcos2_exists)

lemma lcos2_eq_sym: 
  assumes "EqLcos2 l1 a b l2 c d"
  shows "EqLcos2 l2 c d l1 a b" 
  using EqLcos2_def assms by auto

lemma lcos2_uniqueness: 
  assumes "Lcos2 l1 l a b" and
    "Lcos2 l2 l a b"
  shows "l1 EqLTarski l2" 
  by (meson Lcos2_def assms(1) assms(2) l13_7 lcos2_comm)

lemma lcos2_eql_lcos2:
  assumes "Lcos2 la lla a b" and
    "lla EqLTarski llb" and
    "la EqLTarski lb"
  shows "Lcos2 lb llb a b" 
  by (meson Lcos2_def assms(1) assms(2) assms(3) l13_6 lcos_eql_lcos)

lemma lcos2_lg_anga: 
  assumes "Lcos2 lp l a b" 
  shows "Lcos2 lp l a b \<and> QCong lp \<and> QCong l \<and> QCongAAcute a \<and> QCongAAcute b" 
  using Lcos2_def assms lcos_lg_anga by blast

lemma lcos2_eq_trans: 
  assumes "EqLcos2 l1 a b l2 c d" and
    "EqLcos2 l2 c d l3 e f" 
  shows "EqLcos2 l1 a b l3 e f" 
proof -
  obtain lp where "Lcos2 lp l1 a b" and "Lcos2 lp l2 c d" 
    using EqLcos2_def assms(1) by blast
  obtain lq where "Lcos2 lq l2 c d" and "Lcos2 lq l3 e f" 
    using EqLcos2_def assms(2) by blast
  have "lp EqLTarski lq" 
    using \<open>Lcos2 lp l2 c d\<close> \<open>Lcos2 lq l2 c d\<close> lcos2_uniqueness by auto
  thus ?thesis 
    by (metis EqLTarski_def EqLcos2_def \<open>Lcos2 lp l1 a b\<close> \<open>Lcos2 lq l3 e f\<close> lcos2_eql_lcos2)
qed

lemma lcos_eq_lcos2_eq: 
  assumes "QCongAAcute c" and
    "EqLcos la a lb b"
  shows "EqLcos2 la a c lb b c" 
proof -
  obtain lp where "Lcos lp la a" and "Lcos lp lb b" 
    using EqLcos_def assms(2) by blast
  hence "\<not> QCongNull lp \<and> \<not> QCongNull la" 
    using lcos_lg_not_null by blast
  then obtain lq where "Lcos lq lp c" 
    using lcos_exists lcos_lg_anga \<open>Lcos lp la a\<close> assms(1) by blast
  have "Lcos2 lq la a c" 
    using Lcos2_def \<open>Lcos lp la a\<close> \<open>Lcos lq lp c\<close> by blast
  moreover have "Lcos2 lq lb b c" 
    using Lcos2_def \<open>Lcos lp lb b\<close> \<open>Lcos lq lp c\<close> by blast
  ultimately show ?thesis
    using EqLcos2_def by blast
qed

lemma lcos2_lg_not_null:
  assumes "Lcos2 lp l a b" 
  shows "\<not> QCongNull l \<and> \<not> QCongNull lp"
proof -
  obtain la where "Lcos la l a" and "Lcos lp la b" 
    using assms(1) Lcos2_def by auto
  thus ?thesis
    using lcos_lg_not_null by blast
qed

lemma lcos3_lcos_1_2_a: 
  assumes "Lcos3 lp l a b c"
  shows "\<exists> la. Lcos la l a \<and> Lcos2 lp la b c" 
  using Lcos2_def Lcos3_def assms by presburger

lemma lcos3_lcos_1_2_b: 
  assumes "\<exists> la. Lcos la l a \<and> Lcos2 lp la b c" 
  shows "Lcos3 lp l a b c" 
  using Lcos2_def Lcos3_def assms by blast

lemma lcos3_lcos_1_2: 
  shows "Lcos3 lp l a b c \<longleftrightarrow> (\<exists> la. Lcos la l a \<and> Lcos2 lp la b c)" 
  using lcos3_lcos_1_2_a lcos3_lcos_1_2_b by blast

lemma lcos3_lcos_2_1_a:
  assumes "Lcos3 lp l a b c"
  shows "\<exists> lab. Lcos2 lab l a b \<and> Lcos lp lab c" 
  using Lcos2_def assms lcos3_lcos_1_2 by auto

lemma lcos3_lcos_2_1_b:
  assumes "\<exists> lab. Lcos2 lab l a b \<and> Lcos lp lab c" 
  shows "Lcos3 lp l a b c" 
  using Lcos2_def Lcos3_def assms by blast

lemma lcos3_lcos_2_1:
  shows "Lcos3 lp l a b c \<longleftrightarrow> (\<exists> lab. Lcos2 lab l a b \<and> Lcos lp lab c)" 
  using lcos3_lcos_2_1_a lcos3_lcos_2_1_b by blast

lemma lcos3_permut3:
  assumes "Lcos3 lp l a b c"
  shows "Lcos3 lp l b a c" 
proof -
  have "Lcos3 lp l a b c \<longleftrightarrow> (\<exists> lab. Lcos2 lab l a b \<and> Lcos lp lab c)"
    by (simp add: lcos3_lcos_2_1)
  then obtain lab where "Lcos2 lab l a b" and "Lcos lp lab c" 
    using assms by blast
  thus ?thesis 
    using lcos2_comm lcos3_lcos_2_1_b by blast
qed

lemma lcos3_permut1: 
  assumes "Lcos3 lp l a b c"
  shows "Lcos3 lp l a c b" 
proof -
  have "Lcos3 lp l a b c \<longleftrightarrow> (\<exists> lab. Lcos2 lab l a b \<and> Lcos lp lab c)"
    by (simp add: lcos3_lcos_2_1)
  then obtain la where "Lcos la l a" and "Lcos2 lp la b c" 
    using assms lcos3_lcos_1_2_a by blast
  thus ?thesis 
    using lcos2_comm lcos3_lcos_1_2_b by blast
qed

lemma lcos3_permut2: 
  assumes "Lcos3 lp l a b c"
  shows "Lcos3 lp l c b a" 
  using assms lcos3_permut1 lcos3_permut3 by blast

lemma lcos3_exists: 
  assumes "QCong l" and
    "\<not> QCongNull l" and
    "QCongAAcute a" and
    "QCongAAcute b" and
    "QCongAAcute c" 
  shows "\<exists> lp. Lcos3 lp l a b c" 
proof -
  obtain la where "Lcos la l a" 
    using assms(1) assms(2) assms(3) lcos2_exists' by blast
  hence "\<not> QCongNull la \<and> \<not> QCongNull l" 
    using lcos_lg_not_null by blast
  then obtain lab where "Lcos lab la b" 
    using \<open>Lcos la l a\<close> assms(4) lcos_exists lcos_lg_anga by blast
  hence "\<not> QCongNull lab \<and> \<not> QCongNull la" 
    using lcos_lg_not_null by blast
  then obtain lp where "Lcos lp lab c" 
    using \<open>Lcos lab la b\<close> assms(5) lcos2_exists' lcos_lg_anga by blast
  thus ?thesis 
    by (meson \<open>Lcos la l a\<close> assms(4) lcos2_exists lcos3_lcos_1_2 
        lcos_lg_anga lcos_not_lg_null)
qed

lemma lcos3_eq_refl:
  assumes "QCong l" and
    "\<not> QCongNull l" and
    "QCongAAcute a" and
    "QCongAAcute b" and
    "QCongAAcute c"
  shows "EqLcos3 l a b c l a b c" 
  by (simp add: EqLcos3_def assms(1) assms(2) assms(3) assms(4) assms(5) lcos3_exists)

lemma lcos3_eq_sym:
  assumes "EqLcos3 l1 a b c l2 d e f"
  shows "EqLcos3 l2 d e f l1 a b c" 
  using EqLcos3_def assms by auto

lemma lcos3_uniqueness: 
  assumes "Lcos3 l1 l a b c" and
    "Lcos3 l2 l a b c"
  shows "l1 EqLTarski l2" 
proof -
  obtain la lab where "Lcos la l a" and "Lcos lab la b" and "Lcos l1 lab c" 
    using Lcos3_def assms(1) by blast
  obtain la' lab' where "Lcos la' l a" and "Lcos lab' la' b" and "Lcos l2 lab' c" 
    using Lcos3_def assms(2) by blast
  have "la EqLTarski la'" 
    using \<open>Lcos la l a\<close> \<open>Lcos la' l a\<close> lcos_uniqueness by auto
  have "Lcos lab' la b" 
    by (meson \<open>Lcos la l a\<close> \<open>Lcos la' l a\<close> \<open>Lcos lab' la' b\<close> l13_6 lcos_eql_lcos)
  have "lab EqLTarski lab'" 
    using \<open>Lcos lab la b\<close> \<open>Lcos lab' la b\<close> l13_6 by auto
  thus ?thesis 
    using \<open>Lcos l1 lab c\<close> \<open>Lcos l2 lab' c\<close> lcos_eql_lcos lcos_uniqueness by blast
qed

lemma lcos3_eql_lcos3: 
  assumes "Lcos3 la lla a b c" and
    "lla EqLTarski llb" and
    "la EqLTarski lb"
  shows "Lcos3 lb llb a b c" 
proof -
  obtain lpa lpab where "Lcos lpa lla a" and "Lcos lpab lpa b" and "Lcos la lpab c" 
    using Lcos3_def assms(1) by blast
  thus ?thesis
    by (meson Lcos3_def assms(2) assms(3) lcos_eql_lcos lcos_uniqueness)
qed

lemma lcos3_lg_anga: 
  assumes "Lcos3 lp l a b c" 
  shows "Lcos3 lp l a b c \<and> QCong lp \<and> QCong l \<and> QCongAAcute a \<and> QCongAAcute b \<and> QCongAAcute c" 
proof -
  obtain la lab where "Lcos la l a" and "Lcos lab la b" and "Lcos lp lab c" 
    using Lcos3_def assms(1) by blast
  thus ?thesis
    using assms lcos_lg_anga by blast
qed

lemma lcos3_lg_not_null: 
  assumes "Lcos3 lp l a b c"
  shows "\<not> QCongNull l \<and> \<not> QCongNull lp" 
proof -
  obtain la lab where "Lcos la l a" and "Lcos lab la b" and "Lcos lp lab c" 
    using Lcos3_def assms(1) by blast
  thus ?thesis 
    using lcos_lg_not_null by blast
qed

lemma lcos3_eq_trans:
  assumes "EqLcos3 l1 a b c l2 d e f" and
    "EqLcos3 l2 d e f l3 g h i"
  shows "EqLcos3 l1 a b c l3 g h i" 
proof -
  obtain lp where "Lcos3 lp l1 a b c" and "Lcos3 lp l2 d e f" 
    using EqLcos3_def assms(1) by blast
  obtain lq where "Lcos3 lq l2 d e f" and "Lcos3 lq l3 g h i" 
    using EqLcos3_def assms(2) by blast
  thus ?thesis
    by (metis EqLTarski_def EqLcos3_def \<open>Lcos3 lp l1 a b c\<close> \<open>Lcos3 lp l2 d e f\<close>
        lcos3_eql_lcos3 lcos3_uniqueness)
qed

lemma lcos_eq_lcos3_eq: 
  assumes "QCongAAcute c" and
    "QCongAAcute d" and
    "EqLcos la a lb b"
  shows "EqLcos3 la a c d lb b c d" 
proof -
  obtain lp where "Lcos lp la a" and "Lcos lp lb b"
    using EqLcos_def assms(3) by blast
  hence "\<not> QCongNull lp \<and> \<not> QCongNull la" 
    using lcos_lg_not_null by blast
  then obtain lq where "Lcos lq lp c" 
    using lcos_exists \<open>Lcos lp lb b\<close> assms(1) lcos_lg_anga by blast
  hence "\<not> QCongNull lq \<and> \<not> QCongNull lp" 
    using lcos_lg_not_null by blast
  then obtain lm where "Lcos lm lq d" 
    using lcos_exists \<open>Lcos lq lp c\<close> assms(2) lcos_lg_anga by blast
  thus ?thesis
    using EqLcos3_def Lcos3_def \<open>Lcos lp la a\<close> \<open>Lcos lp lb b\<close> \<open>Lcos lq lp c\<close> by blast
qed

lemma lcos2_eq_lcos3_eq: 
  assumes "QCongAAcute e" and
    "EqLcos2 la a b lb c d"
  shows "EqLcos3 la a b e lb c d e" 
proof -
  obtain lp where "Lcos2 lp la a b" and "Lcos2 lp lb c d"
    using EqLcos2_def assms(2) by blast
  hence "\<not> QCongNull la \<and> \<not> QCongNull lp" 
    using lcos2_lg_not_null by blast
  then obtain lq where "Lcos lq lp e" 
    using lcos_exists \<open>Lcos2 lp la a b\<close> assms(1) lcos2_lg_anga by blast
  hence "\<not> QCongNull lq \<and> \<not> QCongNull lp" 
    using lcos_lg_not_null by blast
  have "Lcos3 lq la a b e" 
    using \<open>Lcos lq lp e\<close> \<open>Lcos2 lp la a b\<close> lcos3_lcos_2_1 by blast
  moreover have "Lcos3 lq lb c d e" 
    using \<open>Lcos lq lp e\<close> \<open>Lcos2 lp lb c d\<close> lcos3_lcos_2_1 by auto
  ultimately show ?thesis 
    using EqLcos3_def by blast
qed

end

subsubsection "Vectors"
  (* Gabriel Braun February 2013 *)

context Tarski_Euclidean

begin

lemma eqv_refl:
  shows "A B EqV A B" 
  using EqV_def plg_trivial by blast

lemma eqv_sym: 
  assumes "A B EqV C D"
  shows "C D EqV A B" 
  using EqV_def Plg_perm assms by blast

lemma eqv_trans: 
  assumes "A B EqV C D" and
    "C D EqV E F"
  shows "A B EqV E F"
proof -
  {
    assume "Parallelogram A B D C"
    hence "Parallelogram C D F E \<longrightarrow> ?thesis" 
      using EqV_def plg_comm2 plg_pseudo_trans by blast
    moreover have "C = D \<and> F = E \<longrightarrow> ?thesis" 
      by (metis assms(1) calculation plg_trivial1)
    ultimately have ?thesis 
      using EqV_def assms(2) by blast
  }
  moreover have "A = B \<and> C = D \<longrightarrow> ?thesis" 
    using assms(2) calculation plg_trivial1 by force
  ultimately show ?thesis 
    using EqV_def assms(1) by force
qed

lemma eqv_comm: 
  assumes "A B EqV C D"
  shows "B A EqV D C" 
  by (metis EqV_def assms eqv_sym plg_sym)

lemma vector_construction: 
  shows "\<exists> D. A B EqV C D" 
  by (metis EqV_def eqv_comm plg_existence)

lemma vector_construction_uniqueness:
  assumes "A B EqV C D" and
    "A B EqV C D'" 
  shows "D = D'" 
proof -
  {
    assume "Parallelogram A B D C"
    hence "Parallelogram A B D' C \<longrightarrow> ?thesis" 
      by (meson plg_comm2 plg_uniqueness)
    moreover have "A = B \<and> C = D' \<longrightarrow> ?thesis" 
      using \<open>Parallelogram A B D C\<close> cong_reverse_identity plg_cong by blast
    ultimately have ?thesis 
      using EqV_def assms(2) by force
  }
  moreover have "A = B \<and> C = D \<longrightarrow> ?thesis" 
    by (metis EqV_def assms(2) cong_reverse_identity plg_cong)
  ultimately show ?thesis 
    using EqV_def assms(1) by force
qed

lemma null_vector: 
  assumes "A A EqV B C"
  shows "B = C" 
  using EqV_def assms vector_construction_uniqueness by blast

lemma vector_uniqueness: 
  assumes "A B EqV A C"
  shows "B = C" 
  using assms eqv_refl vector_construction_uniqueness by blast

lemma eqv_trivial: 
  shows "A A EqV B B" 
  by (simp add: EqV_def)

lemma eqv_permut:
  assumes "A B EqV C D" 
  shows "A C EqV B D" 
  using EqV_def assms eqv_refl eqv_sym plg_permut by presburger

lemma eqv_par:
  assumes "A \<noteq> B" and
    "A B EqV C D"
  shows "A B Par C D" 
  by (metis EqV_def Par_cases assms(1) assms(2) eqv_comm par_reflexivity plg_par)

lemma eqv_opp_null:
  assumes "A B EqV B A"
  shows "A = B" 
  by (meson EqV_def assms plg_not_comm plg_trivial)

lemma eqv_sum:
  assumes "A B EqV A' B'" and
    "B C EqV B' C'"
  shows "A C EqV A' C'" 
  by (meson assms(1) assms(2) eqv_permut eqv_trans)

lemma null_sum:
  shows "A B B A SumV C C" 
  using EqV_def SumV_def eqv_permut null_vector by blast

lemma chasles:
  shows "A B B C SumV A C" 
  using SumV_def eqv_permut eqv_refl null_vector by blast

lemma eqv_mid :
  assumes "A B EqV B C"
  shows "B Midpoint A C" 
  using EqV_def assms l7_3_2 plg_comm2 plg_mid_2 by blast

lemma mid_eqv:
  assumes "A Midpoint B C"
  shows "B A EqV A C" 
  by (metis EqV_def assms midpoint_distinct_1 plg_existence plg_mid_2)

lemma sum_sym:
  assumes "A B C D SumV E F"
  shows "C D A B SumV E F"
proof -
  {
    fix D'0
    assume "A B EqV D D'0"
    obtain D' where "C D EqV B D'" 
      using vector_construction by blast
    have "A D' EqV E F" 
      using SumV_def \<open>C D EqV B D'\<close> assms by blast
    have "C B EqV D D'" 
      by (simp add: \<open>C D EqV B D'\<close> eqv_permut)
    have "A D EqV B D'0" 
      by (simp add: \<open>A B EqV D D'0\<close> eqv_permut)
    have "C D'0 EqV E F"
    proof (cases "A = D'0")
      case True
      have "A Midpoint B D" 
        using True \<open>A B EqV D D'0\<close> eqv_comm eqv_mid by blast
      have "Parallelogram C D D' B \<longrightarrow> ?thesis" 
        using Plg_perm True \<open>A D' EqV E F\<close> \<open>A Midpoint B D\<close> eqv_trans mid_eqv plg_mid_2 by blast
      moreover have "C = D \<and> B = D' \<longrightarrow> ?thesis" 
        using \<open>A B EqV D D'0\<close> \<open>A D' EqV E F\<close> eqv_sym eqv_trans by blast
      ultimately show ?thesis 
        using EqV_def \<open>C D EqV B D'\<close> by blast
    next
      case False
      have "Parallelogram C D D' B \<longrightarrow> ?thesis" 
      proof -
        {
          assume "Parallelogram A B D'0 D"
          obtain M0 where "M0 Midpoint C D'" and "M0 Midpoint D B" 
            by (metis EqV_def MidR_uniq_aux \<open>C D EqV B D'\<close> plg_mid_2)
          obtain M1 where "M1 Midpoint A D'0" and "M1 Midpoint B D" 
            using \<open>Parallelogram A B D'0 D\<close> plg_mid by blast
          have "M1 = M0" 
            using \<open>M0 Midpoint D B\<close> \<open>M1 Midpoint B D\<close> l7_17_bis by auto
          have "A \<noteq> D'0 \<or> D' \<noteq> C" 
            by (simp add: False)
          hence "Parallelogram A D' D'0 C"
            using mid_plg [where ?M = "M0"] \<open>M0 Midpoint C D'\<close> \<open>M1 = M0\<close> \<open>M1 Midpoint A D'0\<close> l7_2 by presburger
          hence "?thesis" 
            by (meson EqV_def \<open>A D' EqV E F\<close> eqv_sym eqv_trans)
        }
        moreover have "A \<noteq> B \<and> D'0 \<noteq> B \<longrightarrow> ?thesis" 
          using EqV_def \<open>A B EqV D D'0\<close> calculation by blast
        ultimately show ?thesis 
          using EqV_def False \<open>A B EqV D D'0\<close> plg_trivial1 by blast
      qed
      moreover have "C = D \<and> B = D' \<longrightarrow> ?thesis" 
        using \<open>A B EqV D D'0\<close> \<open>A D' EqV E F\<close> eqv_sym eqv_trans by blast
      ultimately show ?thesis 
        using EqV_def \<open>C D EqV B D'\<close> by blast
    qed
  }
  thus ?thesis using SumV_def 
    by auto
qed

lemma opposite_sum:
  assumes "A B C D SumV E F"
  shows "B A D C SumV F E" 
proof -
  {
    fix D0
    assume "D C EqV A D0"
    obtain D' where "C D EqV B D'" 
      using vector_construction by blast
    hence "A D' EqV E F" 
      using SumV_def assms by blast
    have "D' B EqV A D0" 
      using \<open>C D EqV B D'\<close> \<open>D C EqV A D0\<close> eqv_comm eqv_sym eqv_trans by blast
    hence "B D0 EqV F E" 
      by (meson \<open>A D' EqV E F\<close> eqv_comm eqv_permut eqv_trans)
  }
  thus ?thesis 
    using SumV_def by blast
qed

lemma null_sum_eq:
  assumes "A B B C SumV D D"
  shows "A = C" 
proof -
  obtain D' where "B C EqV B D'" 
    using vector_construction by blast
  hence "A D' EqV D D" 
    using SumV_def assms by blast
  have "A = D'" 
    using \<open>A D' EqV D D\<close> eqv_sym null_vector by blast
  thus ?thesis 
    using \<open>B C EqV B D'\<close> vector_uniqueness by blast
qed

lemma is_to_ise:
  assumes "A B C D SumV E F"
  shows "A B C D SumVExists E F" 
  by (meson SumVExists_def SumV_def assms eqv_sym vector_construction)

lemma ise_to_is:
  assumes "A B C D SumVExists E F"
  shows "A B C D SumV E F" 
proof -
  obtain D' where "B D' EqV C D" 
    using SumVExists_def assms by blast
  thus ?thesis 
    by (metis SumVExists_def SumV_def assms eqv_sym vector_construction_uniqueness)
qed

lemma sum_exists:
  shows "\<exists> E F. A B C D SumV E F" 
  by (metis SumV_def vector_construction vector_construction_uniqueness)

lemma sum_uniqueness:
  assumes "A B C D SumV E F" and
    "A B C D SumV E' F'"
  shows "E F EqV E' F'" 
  by (metis SumV_def assms(1) assms(2) eqv_sym eqv_trans vector_construction)

lemma same_dir_refl: 
  shows "A B SameDir A B" 
proof (cases "A = B")
  case True
  thus ?thesis 
    using SameDir_def by force
next
  case False
  thus ?thesis 
    using SameDir_def by (metis eqv_refl out_trivial)
qed

lemma same_dir_ts:
  assumes "A B SameDir C D"
  shows "\<exists> M. Bet A M D \<and> Bet B M C" 
proof -
  have "(A = B \<and> C = D) \<longrightarrow> ?thesis" 
    using between_trivial by blast
  moreover {
    assume "\<exists> D'. C Out D D' \<and> A B EqV C D'"
    then obtain D' where "C Out D D'" and "A B EqV C D'" 
      by blast
    moreover {
      assume "Parallelogram A B D' C"
      obtain M where "M Midpoint A D'" and "M Midpoint B C" 
        using \<open>Parallelogram A B D' C\<close> plg_mid by blast
      {
        assume "ParallelogramStrict A B D' C"
        have "B C TS A D'" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_two_sides)
        have "A D' TS B C" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_two_sides)
        have "B \<noteq> C" 
          using \<open>A D' TS B C\<close> ts_distincts by presburger
        have "\<not> Col B C D'" 
          using \<open>ParallelogramStrict A B D' C\<close> col_permutation_5 plgs_not_col by blast
        have "B C OS D' D" 
          using \<open>\<not> Col B C D'\<close> calculation(1) l6_6 not_col_distincts out_one_side_1 by blast
        have "B C TS A D" 
          using \<open>B C OS D' D\<close> \<open>B C TS A D'\<close> l9_2 l9_8_2 by blast
        have "\<not> Col A B C" 
          using TS_def \<open>B C TS A D'\<close> by blast
        have "A B ParStrict D' C" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_par_strict)
        have "A C ParStrict B D'" 
          using \<open>ParallelogramStrict A B D' C\<close> plgs_par_strict by blast
        have "A \<noteq> B" 
          using \<open>\<not> Col A B C\<close> not_col_distincts by blast
        have "C D Par A B" 
          by (metis Out_cases \<open>B C TS A D\<close> \<open>\<exists>D'. C Out D D' \<and> A B EqV C D'\<close> 
              eqv_par out_col par_col_par par_symmetry ts_distincts)
        have "A B ParStrict C D" 
          using Col_cases Par_def Par_strict_cases \<open>C D Par A B\<close> \<open>\<not> Col A B C\<close> by blast
        obtain T where "Col T B C" and "Bet A T D" 
          using TS_def \<open>B C TS A D\<close> by blast
        hence "Col A B T \<longrightarrow> ?thesis"  
          by (metis \<open>\<not> Col A B C\<close> between_trivial2 col_trivial_2 colx)
        moreover 
        {
          assume "\<not> Col A B T"
          have "Col C D T \<longrightarrow> ?thesis" 
            by (metis TS_def \<open>A B ParStrict C D\<close> \<open>B C TS A D\<close> \<open>Bet A T D\<close> 
                \<open>Col T B C\<close> bet_col1 between_trivial l6_16_1 par_strict_not_col_3)
          moreover 
          {
            assume "\<not> Col C D T"
            have "Bet T B C \<longrightarrow> ?thesis" 
              using Par_strict_cases \<open>A B ParStrict C D\<close> \<open>Bet A T D\<close> 
                \<open>Col T B C\<close> \<open>\<not> Col A B C\<close> \<open>\<not> Col A B T\<close> between_trivial 
                between_trivial2 impossible_case_4_2 not_col_permutation_2 by blast
            moreover 
            {
              assume "Bet B C T"
              have "C D OS T A" 
                by (metis \<open>Bet A T D\<close> \<open>\<not> Col C D T\<close> bet_out_1 not_col_distincts out_one_side_1)
              have "C D OS T B"  
                using \<open>A B ParStrict C D\<close> \<open>C D OS T A\<close> one_side_transitivity 
                  pars__os3412 by blast
              moreover have "C D TS T B" 
                using \<open>B \<noteq> C\<close> \<open>Bet B C T\<close> \<open>\<not> Col C D T\<close> bet__ts 
                  between_symmetry by presburger
              ultimately have False 
                using l9_9_bis by auto
              hence ?thesis 
                by blast
            }
            moreover have "Bet C T B \<longrightarrow> ?thesis" 
              using \<open>Bet A T D\<close> between_symmetry by blast
            ultimately have ?thesis 
              using Col_def \<open>Col T B C\<close> by blast
          }
          ultimately have ?thesis 
            by blast
        }
        ultimately have ?thesis 
          by blast
      }
      moreover 
      {
        assume "ParallelogramFlat A B D' C"
        hence "Bet C D' A \<and> Bet D' A B \<or> Bet C A D' \<and> Bet A D' B \<or> 
                Bet A C B \<and> Bet C B D' \<or> Bet A B C \<and> Bet B C D'" 
          by (simp add: plgf_bet)
        have "A = D' \<longrightarrow> ?thesis" 
          by (metis Midpoint_def 
              \<open>\<And>thesis. (\<And>M. \<lbrakk>M Midpoint A D'; M Midpoint B C\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
              between_identity not_bet_distincts)
        moreover 
        {
          assume "A \<noteq> D'"
          {
            assume "B = C"
            have "A = D' \<or> B Midpoint A D'" 
              using \<open>A B EqV C D'\<close> \<open>B = C\<close> eqv_mid by auto
            moreover have "A = D' \<longrightarrow> ?thesis" 
              using \<open>A \<noteq> D'\<close> by blast
            moreover 
            {
              assume "B Midpoint A D'"
              have "Bet B D D' \<longrightarrow> Bet A B D" 
                using \<open>B Midpoint A D'\<close> between_inner_transitivity midpoint_bet by blast
              moreover have "Bet B D' D \<longrightarrow> Bet A B D" 
                by (metis \<open>B Midpoint A D'\<close> midpoint_bet midpoint_not_midpoint 
                    outer_transitivity_between)
              ultimately have "Bet A B D" 
                using Out_def \<open>B = C\<close> \<open>C Out D D'\<close> by blast
              hence ?thesis 
                using not_bet_distincts by blast  
            }
            ultimately have ?thesis 
              by blast
          }
          moreover 
          {
            assume "B \<noteq> C"
            have "Bet C D' A \<and> Bet D' A B \<longrightarrow> ?thesis" 
              by (metis Bet_cases \<open>A \<noteq> D'\<close> between_trivial2 outer_transitivity_between2)
            moreover have "Bet C A D' \<and> Bet A D' B \<longrightarrow> ?thesis" 
              by (meson Bet_cases \<open>A \<noteq> D'\<close> between_trivial2 outer_transitivity_between)
            moreover  
            {
              assume "Bet A C B" and "Bet C B D'"
              have "Bet A C D" 
                by (metis \<open>A B EqV C D'\<close> \<open>B \<noteq> C\<close> \<open>Bet A C B\<close> \<open>Bet C B D'\<close> 
                    \<open>\<exists>D'. C Out D D' \<and> A B EqV C D'\<close> bet_out bet_out_out_bet l6_6 
                    not_bet_distincts vector_construction_uniqueness)
              moreover have "Bet B C C" 
                by (simp add: between_trivial)
              ultimately have ?thesis 
                by blast
            }
            moreover have "Bet A B C \<and> Bet B C D' \<longrightarrow> ?thesis" 
              by (meson Out_cases \<open>B \<noteq> C\<close> \<open>C Out D D'\<close> bet_out_1 bet_out_out_bet l5_3)
            ultimately have ?thesis 
              using \<open>Bet C D' A \<and> Bet D' A B \<or> Bet C A D' \<and> 
                       Bet A D' B \<or> Bet A C B \<and> Bet C B D' \<or> Bet A B C \<and> Bet B C D'\<close> 
              by fastforce
          }
          ultimately have ?thesis 
            by blast
        }
        ultimately have ?thesis 
          by blast
      }
      ultimately have ?thesis 
        using Parallelogram_def \<open>Parallelogram A B D' C\<close> by blast
    }
    moreover have "(A = B \<and> C = D') \<longrightarrow> ?thesis" 
      using calculation(1) out_diff2 by blast
    ultimately have ?thesis 
      using EqV_def by blast
  }
  ultimately show ?thesis 
    using SameDir_def assms by presburger
qed

lemma one_side_col_out:
  assumes "Col A X Y" and
    "A B OS X Y" 
  shows "A Out X Y" 
  using assms(1) assms(2) col_one_side_out by force

lemma par_ts_same_dir:
  assumes "A B ParStrict C D" and
    "\<exists> M. Bet A M D \<and> Bet B M C"
  shows "A B SameDir C D" 
proof -
  obtain M where "Bet A M D" and "Bet B M C" 
    using assms(2) by force
  obtain D' where "A B EqV C D'" 
    using vector_construction by blast
  have "A \<noteq> B" 
    using assms(1) par_strict_neq1 by blast
  have "C \<noteq> D" 
    using assms(1) par_strict_distinct by blast
  have "A \<noteq> M" 
    using NCol_perm \<open>Bet B M C\<close> assms(1) bet_col par_strict_not_col_1 by blast
  have "B = D' \<longrightarrow> C Out D D'" 
    by (metis Col_def EqV_def Plg_perm \<open>A B EqV C D'\<close> assms(1) 
        not_bet_distincts par_strict_not_col_3 plg_not_comm)
  moreover 
  {
    assume "B \<noteq> D'"
    {
      assume "Parallelogram A B D' C"
      have "A B Par D' C" 
        using \<open>A \<noteq> B\<close> \<open>B \<noteq> D'\<close> \<open>Parallelogram A B D' C\<close> plg_par by auto
      have "Col C D D'" 
        by (metis Par_strict_cases \<open>Parallelogram A B D' C\<close> assms(1) 
            col_permutation_4 ncol124_plg__pars1234 par_id_1 
            par_strict_not_col_1 par_strict_trans)
      {
        assume "ParallelogramStrict A B D' C"
        have "A D' TS B C" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_two_sides)
        have "B C TS A D'" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_two_sides)
        have "B C TS A D" 
          by (metis NCol_perm Par_strict_cases assms(1) assms(2) bet_col 
              l9_18_R2 par_strict_not_col_2)
        have "B C OS D D'" 
        proof (rule l9_8_1 [where ?C = "A"])
          show "B C TS D A" 
            using \<open>B C TS A D\<close> l9_2 by blast
          show "B C TS D' A" 
            by (simp add: \<open>B C TS A D'\<close> l9_2)
        qed
        hence "C Out D D'" 
          using one_side_col_out [where ?B = "B"] \<open>B C OS D D'\<close> calculation 
            invert_one_side \<open>Col C D D'\<close> by blast
      }
      moreover have "ParallelogramFlat A B D' C \<longrightarrow> C Out D D'" 
        using ParallelogramFlat_def assms(1) par_strict_not_col_1 by force
      ultimately have "C Out D D'" 
        using Parallelogram_def \<open>Parallelogram A B D' C\<close> by blast
    }
    moreover have "(A = B \<and> C = D') \<longrightarrow> C Out D D'" 
      by (simp add: \<open>A \<noteq> B\<close>)
    ultimately have "C Out D D'" 
      using EqV_def \<open>A B EqV C D'\<close> by presburger
  }
  ultimately have "C Out D D'" 
    by blast
  hence "\<exists> D'. C Out D D' \<and> A B EqV C D'" 
    using \<open>A B EqV C D'\<close> by blast
  thus ?thesis 
    by (simp add: SameDir_def)
qed

lemma same_dir_out: 
  assumes "A B SameDir A C"
  shows "A Out B C \<or> (A = B \<and> A = C)"  
proof -
  have "A = B \<and> A = C \<or> (\<exists> D'. A Out C D' \<and> A B EqV A D')" 
    using SameDir_def assms by presburger
  moreover
  have "(\<exists> D'. A Out C D' \<and> A B EqV A D') \<longrightarrow> ?thesis" 
    using l6_6 vector_uniqueness by blast
  ultimately show ?thesis
    by blast
qed

lemma same_dir_out1: 
  assumes "A B SameDir B C"
  shows "A Out B C \<or> (A = B \<and> A = C)"  
proof -
  have "A = B \<and> B = C \<or> (\<exists> D'. B Out C D' \<and> A B EqV B D')" 
    using SameDir_def assms by presburger
  moreover have "(\<exists> D'. B Out C D' \<and> A B EqV B D') \<longrightarrow> ?thesis" 
    by (metis assms bet_neq23__neq bet_out_1 between_symmetry same_dir_out same_dir_ts)
  ultimately show ?thesis 
    by blast
qed

lemma same_dir_null:
  assumes "A A SameDir B C"
  shows "B = C"  
proof -
  have "A = A \<and> B = C \<or> (\<exists> D'. B Out C D' \<and> A A EqV B D')" 
    using SameDir_def assms by presburger
  moreover have "(\<exists> D'. B Out C D' \<and> A A EqV B D') \<longrightarrow> ?thesis" 
    using null_vector out_distinct by blast
  ultimately show ?thesis 
    by blast
qed

lemma plgs_out_plgs:
  assumes "ParallelogramStrict A B C D" and
    "A Out B B'" and
    "D Out C C'" and
    "Cong A B' D C'" 
  shows "ParallelogramStrict A B' C' D" 
proof -
  have "A D OS C B" 
    using assms(1) plgs_comm2 plgs_one_side plgs_permut by blast
  have "C B OS A D" 
    using assms(1) plgs_comm2 plgs_one_side plgs_permut by blast
  have "A \<noteq> B'"       
    using assms(2) out_distinct by blast
  have "D \<noteq> C'" 
    using assms(3) out_distinct by blast
  have "A B ParStrict C D" 
    by (simp add: assms(1) plgs_pars_1)
  have "A B' Par D C'"
  proof (rule par_col_par_2 [where ?B ="B"])
    show "A \<noteq> B'"       
      by (simp add: \<open>A \<noteq> B'\<close>)
    show "Col A B B'" 
      by (simp add: assms(2) out_col)
    show "A B Par D C'"
      by (metis Col_def Out_def \<open>A B ParStrict C D\<close> assms(3) 
          not_col_distincts par_col2_par par_strict_par)
  qed
  moreover have "A B ParStrict D C' \<longrightarrow> A B' ParStrict D C'" 
    by (metis Col_cases Par_def calculation par_strict_not_col_3)
  ultimately have "A B' ParStrict D C'" 
    using Par_strict_perm \<open>A B ParStrict C D\<close> \<open>D \<noteq> C'\<close> assms(3) 
      out_col par_strict_col_par_strict by blast
  have "A D OS B B'" 
    using \<open>A D OS C B\<close> assms(2) one_side_symmetry one_side_transitivity 
      out_out_one_side by blast
  have "A D OS C C'" 
    using \<open>A D OS C B\<close> assms(3) col123__nos invert_one_side out_one_side by blast
  have "A D OS B' C'" 
    by (meson \<open>A D OS B B'\<close> \<open>A D OS C B\<close> \<open>A D OS C C'\<close> 
        one_side_symmetry one_side_transitivity)
  then obtain M where "M Midpoint A C'" and "M Midpoint B' D" 
    using par_cong_mid_os \<open>A B' ParStrict D C'\<close> assms(4) by blast
  thus ?thesis using mid_plgs 
    using Par_strict_cases \<open>A B' ParStrict D C'\<close> par_strict_not_col_1 by blast
qed

lemma plgs_plgs_bet:
  assumes "ParallelogramStrict A B C D" and
    "Bet A B B'" and
    "ParallelogramStrict A B' C' D"
  shows "Bet D C C'" 
proof -
  have "A B ParStrict C D \<and> A D ParStrict B C" 
    by (simp add: assms(1) plgs_par_strict)
  hence "A B Par C D" 
    by (simp add: par_strict_par)
  moreover have "A B Par C' D" 
    using par_col_par_2 [where ?B = "B'"] 
    by (metis Col_def assms(1) assms(2) assms(3) between_symmetry 
        par_strict_par plgs_comm2 plgs_not_comm_1 plgs_pars_1)
  ultimately have "Col C' C D \<and> Col D C D"
    using parallel_uniqueness [where ?A1.0 ="A" and ?A2.0="B"  and ?P="D"]
    by (metis col_trivial_3)
  hence "Col C' C D"
    by simp
  moreover have "Bet C' C D \<longrightarrow> ?thesis" 
    using between_symmetry by blast
  moreover
  {
    assume "Bet C D C'"
    have "B C OS D A" 
      by (simp add: assms(1) plgs_one_side plgs_permut)
    have "D A OS B C" 
      by (simp add: assms(1) plgs_one_side plgs_permut)
    have "B' C' OS D A" 
      by (simp add: assms(3) plgs_one_side plgs_permut)
    have "D A OS B' C'" 
      by (simp add: assms(3) plgs_one_side plgs_permut)
    have "D A OS B' B"
    proof (rule out_one_side_1 [where ?X = "A"])
      show "\<not> Col D A B'" 
        using \<open>D A OS B' C'\<close> col123__nos by blast
      show "Col D A A" 
        by (simp add: col_trivial_2)
      show "A Out B' B" 
        by (metis \<open>A B Par C' D\<close> assms(2) bet_out l6_6 par_neq1)
    qed
    hence "D A OS B C'" 
      using \<open>D A OS B' C'\<close> one_side_symmetry one_side_transitivity by blast
    hence "D A OS C C'" 
      using \<open>D A OS B C\<close> one_side_symmetry one_side_transitivity by blast
    moreover have "D A TS C C'" 
      using \<open>Bet C D C'\<close> \<open>D A OS C C'\<close> l9_17 os_distincts by blast
    ultimately have False 
      by (simp add: l9_9_bis)
  } 
  moreover 
  {
    assume "Bet D C' C"
    have "ParallelogramStrict B C D A" 
      by (simp add: assms(1) plgs_permut)
    have "ParallelogramStrict D A B' C'" 
      by (simp add: assms(3) plgs_permut)
    have "C = C' \<longrightarrow> ?thesis" 
      using \<open>Bet D C' C\<close> by blast
    moreover 
    {
      assume "C \<noteq> C'"
      have "Parallelogram B C C' B'" 
        using \<open>ParallelogramStrict B C D A\<close> \<open>ParallelogramStrict D A B' C'\<close> 
          plgs_pseudo_trans by auto
      hence "ParallelogramStrict B C C' B'" 
        by (metis NCol_perm \<open>C \<noteq> C'\<close> \<open>Col C' C D \<and> Col D C D\<close> assms(3) 
            colx ncol234_plg__plgs not_col_distincts plgs_not_col)
      have "B C OS C' B'" 
        by (simp add: \<open>ParallelogramStrict B C C' B'\<close> plgs_one_side)
      have "C' B' OS B C" 
        by (simp add: \<open>ParallelogramStrict B C C' B'\<close> plgs_one_side)
      have "B C OS D A" 
        using \<open>ParallelogramStrict B C D A\<close> plgs_one_side by blast
      have "D A OS B C" 
        using \<open>ParallelogramStrict B C D A\<close> plgs_one_side by blast
      have "B C TS A B'" 
        by (metis \<open>A B ParStrict C D \<and> A D ParStrict B C\<close> \<open>B C OS C' B'\<close> assms(2) 
            bet__ts os_distincts par_strict_not_col_3)
      moreover have "B C OS C' D" 
        by (metis \<open>B C OS C' B'\<close> \<open>Bet D C' C\<close> bet_out_1 col123__nos invert_one_side 
            os_distincts out_one_side)
      have "B C OS A B'" 
        by (meson \<open>B C OS C' B'\<close> \<open>B C OS C' D\<close> \<open>B C OS D A\<close> one_side_symmetry 
            one_side_transitivity)
      ultimately have ?thesis 
        by (simp add: l9_9)
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis
    using Col_def by blast
qed

lemma plgf_plgf_bet:
  assumes "ParallelogramFlat A B C D" and
    "Bet A B B'" and
    "ParallelogramFlat A B' C' D"
  shows "Bet D C C'" 
proof (cases "A = B") 
  case True
  thus ?thesis 
    using assms(1) cong_reverse_identity not_bet_distincts plgf_cong by blast
next
  case False
  hence "A \<noteq> B" 
    by blast
  obtain P where "\<not> Col A B P" 
    using False not_col_exists by blast
  obtain Q where "Parallelogram A B P Q" 
    using False plg_existence by blast
  have "ParallelogramStrict A B P Q" 
    using \<open>Parallelogram A B P Q\<close> \<open>\<not> Col A B P\<close> not_col_distincts 
      parallel_2_plg plg_par by blast
  have "ParallelogramStrict C D Q P" 
  proof (rule plgf_plgs_trans [where ?C = "A" and ?D = "B"])
    show "C \<noteq> D" 
      using False assms(1) plgf_not_comm1 by blast
    show "ParallelogramFlat C D A B" 
      by (simp add: assms(1) plgf_sym)
    show "ParallelogramStrict A B P Q" 
      by (simp add: \<open>ParallelogramStrict A B P Q\<close>)
  qed
  have "A \<noteq> B'" 
    using False assms(2) between_identity by blast
  obtain P' where "A B' EqV Q P'" 
    using vector_construction by blast
  {
    assume "Parallelogram A B' P' Q"
    have "B \<noteq> P" 
      using \<open>\<not> Col A B P\<close> col_trivial_2 by blast
    have "B' \<noteq> P'" 
      by (metis \<open>Parallelogram A B' P' Q\<close> \<open>ParallelogramStrict A B P Q\<close>
          cong_identity_inv plg_cong plgs_diff)
    have "A B' Par P Q" 
      by (meson False \<open>A \<noteq> B'\<close> \<open>B \<noteq> P\<close> \<open>Parallelogram A B P Q\<close> assms(2) 
          bet_col par_col_par_2 plg_par)
    have "Col P' P Q \<and> Col Q P Q" 
      using parallel_uniqueness by (metis Par_cases \<open>A B' EqV Q P'\<close> 
          \<open>A B' Par P Q\<close> \<open>A \<noteq> B'\<close> eqv_par par_id_4 par_trans)
    hence "Col P' P Q" 
      by simp
    have "ParallelogramStrict A B' P' Q" 
      by (meson \<open>A \<noteq> B'\<close> \<open>Parallelogram A B' P' Q\<close> \<open>ParallelogramStrict A B P Q\<close> 
          assms(2) bet_col col_trivial_3 colx ncol124_plg__plgs 
          parallelogram_strict_not_col_4)
    have "ParallelogramStrict D C' P' Q"
      using plgf_plgs_trans [where ?C ="B'" and ?D="A"] 
      by (metis \<open>A \<noteq> B'\<close> \<open>ParallelogramStrict A B' P' Q\<close> assms(3) 
          plgf_not_comm1 plgf_plgs_trans plgf_sym plgs_comm2)
    have "Bet Q P P'" 
      using plgs_plgs_bet \<open>ParallelogramStrict A B P Q\<close> 
        \<open>ParallelogramStrict A B' P' Q\<close> assms(2) by blast
    have ?thesis 
      using plgs_plgs_bet [where ?A="Q" and ?B="P" and ?B'="P'"] \<open>Bet Q P P'\<close> 
        \<open>ParallelogramStrict C D Q P\<close> \<open>ParallelogramStrict D C' P' Q\<close> 
        plgs_comm2 plgs_sym by blast
  }
  thus ?thesis 
    using EqV_def \<open>A B' EqV Q P'\<close> \<open>A \<noteq> B'\<close> by blast
qed

lemma plg_plg_bet:
  assumes "Parallelogram A B C D" and
    "Bet A B B'" and
    "Parallelogram A B' C' D"
  shows "Bet D C C'" 
proof (cases "A = B")
  case True
  thus ?thesis 
    using assms(1) cong_reverse_identity not_bet_distincts plg_cong by blast
next
  case False
  hence "A \<noteq> B"
    by blast
  show ?thesis 
  proof (cases "B = C")
    case True
    thus ?thesis 
      by (metis assms(1) assms(2) assms(3) cong_diff cong_reverse_identity plg_cong)
  next
    case False
    hence "B \<noteq> C"
      by blast
    have "A \<noteq> B'" 
      using \<open>A \<noteq> B\<close> assms(2) between_identity by blast
    have "B' \<noteq> C'" 
      by (metis False Plg_perm assms(1) assms(3) plg_not_comm)
    have "A B Par C D \<and> A D Par B C" 
      by (simp add: False \<open>A \<noteq> B\<close> assms(1) plg_par)
    have "A B' Par C' D \<and> A D Par B' C'" 
      by (simp add: \<open>A \<noteq> B'\<close> \<open>B' \<noteq> C'\<close> assms(3) plg_par_1 plg_par_2)
    have "A B Par C' D" 
      using Bet_cases Col_def \<open>A B' Par C' D \<and> A D Par B' C'\<close> \<open>A \<noteq> B\<close> 
        assms(2) par_col_par_2 by blast
    have "Col C' C D \<and> Col D C D" 
      using \<open>A B Par C D \<and> A D Par B C\<close> \<open>A B Par C' D\<close> col_trivial_3 
        parallel_uniqueness by blast
    {
      assume "ParallelogramStrict A B C D" and "ParallelogramFlat A B' C' D"
      hence False 
        by (metis Col_cases ParallelogramFlat_def \<open>A B' Par C' D \<and> A D Par B' C'\<close> 
            \<open>Col C' C D \<and> Col D C D\<close> colx par_distincts 
            parallelogram_strict_not_col_3 plgf_sym)
    }
    moreover 
    {
      assume "ParallelogramStrict A B C D" and "ParallelogramStrict A B' C' D"
      hence ?thesis 
        using plgs_plgs_bet [where ?A = "A" and ?B = "B" and ?B'= "B'"] assms(2) by blast
    }
    moreover 
    have "ParallelogramFlat A B C D \<and> ParallelogramFlat A B' C' D \<longrightarrow> ?thesis"
      using plgf_plgf_bet assms(2) by blast
    moreover 
    {
      assume "ParallelogramFlat A B C D" and "ParallelogramStrict A B' C' D"
      hence False 
        by (metis Col_cases ParallelogramFlat_def \<open>A B Par C D \<and> A D Par B C\<close> 
            \<open>Col C' C D \<and> Col D C D\<close> colx par_distincts 
            parallelogram_strict_not_col_3 plgf_sym)
    }
    ultimately show ?thesis 
      using Parallelogram_def assms(1) assms(3) by presburger
  qed
qed

lemma plgf_out_plgf:
  assumes "ParallelogramFlat A B C D" and
    "A Out B B'" and
    "D Out C C'" and
    "Cong A B' D C'"
  shows "ParallelogramFlat A B' C' D" 
proof -
  have "A \<noteq> B" 
    using assms(2) out_distinct by blast
  have "A \<noteq> B'" 
    using assms(2) out_diff2 by blast
  have "D \<noteq> C" 
    using assms(3) out_distinct by blast
  have "D \<noteq> C'" 
    using assms(3) out_distinct by blast
  obtain P where "\<not> Col A B P" 
    using \<open>A \<noteq> B\<close> not_col_exists by fastforce
  obtain Q where "Parallelogram A B P Q" 
    using \<open>A \<noteq> B\<close> plg_existence by blast
  have "ParallelogramStrict A B P Q" 
    using ParallelogramFlat_def Parallelogram_def \<open>Parallelogram A B P Q\<close> 
      \<open>\<not> Col A B P\<close> by presburger
  have "ParallelogramStrict C D Q P" 
    by (metis \<open>D \<noteq> C\<close> \<open>ParallelogramStrict A B P Q\<close> assms(1) plgf_plgs_trans plgf_sym)
  obtain P' where " A B' EqV Q P'" 
    using vector_construction by blast
  have "B \<noteq> P" 
    using \<open>\<not> Col A B P\<close> not_col_distincts by auto
  have "B' \<noteq> P'" 
    by (metis EqV_def \<open>A B' EqV Q P'\<close> \<open>ParallelogramStrict A B P Q\<close> 
        eqv_permut plg_not_comm_R1 plgs_diff)
  have "A B Par P Q \<and> A Q Par B P" 
    using plg_par \<open>A \<noteq> B\<close> \<open>B \<noteq> P\<close> \<open>Parallelogram A B P Q\<close> by blast
  moreover have "A B' Par P' Q \<and> A Q Par B' P'" 
    using plg_par EqV_def \<open>A B' EqV Q P'\<close> \<open>A \<noteq> B'\<close> \<open>B' \<noteq> P'\<close> by auto
  ultimately have "Col Q P P'" 
    by (meson assms(2) col_par_par_col col_permutation_4 out_col par_left_comm par_right_comm)
  {
    assume "ParallelogramFlat A B' P' Q"
    hence "Col A B' P' \<and> Col A B' Q \<and> Cong A B' P' Q \<and> Cong A Q P' B' \<and> (A \<noteq> P' \<or> B' \<noteq> Q)" 
      using ParallelogramFlat_def by force
    hence False 
      by (metis \<open>ParallelogramStrict A B P Q\<close> assms(2) col_trivial_3 
          colx l6_3_1 out_col plgs_not_col)
  }
  hence "ParallelogramStrict A B' P' Q" 
    using EqV_def Parallelogram_def \<open>A B' EqV Q P'\<close> \<open>A \<noteq> B'\<close> by blast
  hence "A B' Par P Q" 
    using \<open>A B Par P Q \<and> A Q Par B P\<close> \<open>A \<noteq> B'\<close> assms(2) out_col par_col_par_2 by blast
  have "P \<noteq> Q" 
    using \<open>A B' Par P Q\<close> par_distincts by auto
  have "P' \<noteq> Q" 
    using \<open>A B' Par P' Q \<and> A Q Par B' P'\<close> par_distincts by auto
  have "ParallelogramStrict D C' P' Q" 
  proof(rule plgs_out_plgs [where ?B="C" and ?C="P"])
    show "ParallelogramStrict D C P Q"         
      using \<open>ParallelogramStrict C D Q P\<close> plgs_comm2 by blast
    show "D Out C C'"         
      using assms(3) by auto
    show "Q Out P P'"         
      using EqV_def Out_def \<open>A B' EqV Q P'\<close> \<open>P \<noteq> Q\<close> \<open>P' \<noteq> Q\<close> 
        \<open>Parallelogram A B P Q\<close> assms(2) plg_plg_bet by auto
    show "Cong D C' Q P'" 
      using \<open>ParallelogramStrict A B' P' Q\<close> assms(4) cong_inner_transitivity 
        cong_right_commutativity plgs_cong_1 by blast
  qed
  have "Parallelogram A B' C' D" 
    by (meson \<open>ParallelogramStrict A B' P' Q\<close> \<open>ParallelogramStrict D C' P' Q\<close> 
        plgs_permut plgs_pseudo_trans)
  thus ?thesis 
    by (metis Col_cases ParallelogramFlat_def \<open>A \<noteq> B\<close> \<open>D \<noteq> C\<close> assms(1) assms(2) 
        assms(3) col_trivial_3 colx out_col plg_col_plgf)
qed

lemma plg_out_plg: 
  assumes "Parallelogram A B C D" and
    "A Out B B'" and
    "D Out C C'" and
    "Cong A B' D C'"
  shows "Parallelogram A B' C' D" 
proof -
  have "ParallelogramStrict A B C D \<longrightarrow> ?thesis"     
    using Parallelogram_strict_Parallelogram assms(2) assms(3) assms(4) 
      plgs_out_plgs by blast
  moreover have "ParallelogramFlat A B C D \<longrightarrow> ?thesis"     
    using Parallelogram_def assms(2) assms(3) assms(4) plgf_out_plgf by blast
  ultimately show ?thesis
    using Parallelogram_def assms(1) by blast
qed

lemma same_dir_sym:
  assumes "A B SameDir C D"
  shows "C D SameDir A B" 
proof (cases "A = B")
  case True
  thus ?thesis 
    using SameDir_def assms same_dir_null by presburger
next
  case False
  have "(A = B \<and> C = D) \<longrightarrow> ?thesis" 
    using False by auto
  moreover 
  {
    assume "\<exists> D'. C Out D D' \<and> A B EqV C D'"
    then obtain D' where "C Out D D'" and "A B EqV C D'" 
      by blast
    obtain B' where "C D EqV A B'" 
      using vector_construction by blast
    have "Parallelogram A B D' C \<or> (A = B \<and> C = D')" 
      using EqV_def \<open>A B EqV C D'\<close> by force
    hence "Parallelogram A B D' C" 
      by (simp add: False)
    have "Parallelogram C D B' A \<or> (C = D \<and> A = B')" 
      using EqV_def \<open>C D EqV A B'\<close> by auto
    hence "Parallelogram C D B' A" 
      using Out_def \<open>C Out D D'\<close> by blast
    {
      assume "Parallelogram A B D' C" and "Parallelogram C D B' A"
      have "B \<noteq> A" 
        using False by auto
      moreover have "B' \<noteq> A" 
        by (metis \<open>C Out D D'\<close> \<open>Parallelogram C D B' A\<close> out_diff1 plg_not_comm_R1)
      moreover have "Bet A B B' \<or> Bet A B' B" 
      proof -
        have "Bet C D D' \<longrightarrow> ?thesis" 
          using EqV_def False \<open>A B EqV C D'\<close> \<open>Parallelogram C D B' A\<close>
            eqv_sym plg_plg_bet by blast
        moreover have "Bet C D' D \<longrightarrow> ?thesis" 
          using Plg_perm \<open>Parallelogram A B D' C\<close> \<open>Parallelogram C D B' A\<close> 
            plg_plg_bet by blast
        ultimately show ?thesis
          using Out_def \<open>C Out D D'\<close> by blast
      qed
      ultimately have "A Out B B'" 
        by (simp add: Out_def)
    }
    hence "A Out B B'" 
      using \<open>Parallelogram A B D' C\<close> \<open>Parallelogram C D B' A\<close> by blast
    moreover have "C D EqV A B'" 
      by (simp add: \<open>C D EqV A B'\<close>)
    ultimately have "\<exists> D'0. A Out B D'0 \<and> C D EqV A D'0" 
      by blast
    hence ?thesis 
      by (simp add: SameDir_def)
  }
  ultimately show ?thesis 
    using SameDir_def assms by force
qed

lemma same_dir_trans: 
  assumes "A B SameDir C D" and
    "C D SameDir E F"
  shows "A B SameDir E F" 
proof -
  have "(A = B \<and> C = D) \<or> (\<exists> D'. C Out D D' \<and> A B EqV C D')" 
    using SameDir_def assms(1) by presburger
  moreover have "(A = B \<and> C = D) \<longrightarrow> ?thesis" 
    using SameDir_def assms(2) same_dir_null by blast
  moreover 
  {
    assume "\<exists> D'. C Out D D' \<and> A B EqV C D'"
    then obtain D' where "C Out D D'" and "A B EqV C D'" 
      by blast
    have "(C = D \<and> E = F) \<or> (\<exists> D'. E Out F D' \<and> C D EqV E D')" 
      using SameDir_def assms(2) by auto
    moreover have "(C = D \<and> E = F) \<longrightarrow> ?thesis" 
      using Out_def \<open>C Out D D'\<close> by force
    moreover 
    {
      assume "\<exists> D'. E Out F D' \<and> C D EqV E D'"
      then obtain F' where "E Out F F'" and "C D EqV E F'"
        by blast
      have "A = B \<longrightarrow> (\<exists> D'0. E Out F D'0 \<and> A B EqV E D'0)"           
        by (metis Out_def \<open>A B EqV C D'\<close> \<open>C Out D D'\<close> null_vector)
      moreover 
      {
        assume "A \<noteq> B"
        obtain F'' where "A B EqV E F''" 
          using vector_construction by blast
        have "C \<noteq> D" 
          using Out_def \<open>C Out D D'\<close> by blast
        have "C \<noteq> D'" 
          using \<open>C Out D D'\<close> out_distinct by blast
        have "E \<noteq> F" 
          using \<open>E Out F F'\<close> l6_3_1 by blast
        have "E \<noteq> F'" 
          using \<open>E Out F F'\<close> out_diff2 by blast
        have "Parallelogram A B D' C \<or> (A = B \<and> C = D')" 
          using EqV_def \<open>A B EqV C D'\<close> by blast
        hence "Parallelogram A B D' C" 
          using \<open>A \<noteq> B\<close> by blast 
        have "Parallelogram C D F' E \<or> (C = D \<and> E = F')" 
          using EqV_def \<open>C D EqV E F'\<close> by auto
        hence "Parallelogram C D F' E" 
          using \<open>C \<noteq> D\<close> by blast
        have "Parallelogram A B F'' E \<or> (A = B \<and> E = F'')" 
          using EqV_def \<open>A B EqV E F''\<close> by presburger
        hence "Parallelogram A B F'' E" 
          using \<open>A \<noteq> B\<close> by blast
        have "Bet C D D' \<or> Bet C D' D" 
          using Out_def \<open>C Out D D'\<close> by presburger
        have "Bet E F F' \<or> Bet E F' F" 
          using Out_def \<open>E Out F F'\<close> by force
        have "Parallelogram C D' F'' E" 
          using Plg_perm \<open>C \<noteq> D'\<close> \<open>Parallelogram A B D' C\<close> \<open>Parallelogram A B F'' E\<close> 
            plg_pseudo_trans by blast
        have "E Out F F''" 
        proof -
          have "Parallelogram A B D' C \<or> (A = B \<and> C = D')" 
            by (simp add: \<open>Parallelogram A B D' C \<or> A = B \<and> C = D'\<close>)
          moreover have "Parallelogram C D F' E \<or> (C = D \<and> E = F')" 
            using \<open>Parallelogram C D F' E\<close> by blast
          moreover have "Parallelogram A B F'' E \<or> (A = B \<and> E = F'')" 
            using \<open>Parallelogram A B F'' E \<or> A = B \<and> E = F''\<close> by blast
          moreover have "(A = B \<and> C = D') \<longrightarrow> ?thesis" 
            by (simp add: \<open>A \<noteq> B\<close>)
          moreover have "Parallelogram A B D' C \<and> Parallelogram C D F' E \<and> 
                           Parallelogram A B F'' E"
            using \<open>Parallelogram A B D' C\<close> \<open>Parallelogram A B F'' E\<close> 
              \<open>Parallelogram C D F' E\<close> by auto
          moreover
          {
            assume "Parallelogram A B D' C" and
              "Parallelogram C D F' E" and 
              "Parallelogram A B F'' E"
            have "Bet C D D' \<or> Bet C D' D" 
              by (simp add: \<open>Bet C D D' \<or> Bet C D' D\<close>)
            moreover have "Bet E F F' \<or> Bet E F' F" 
              using \<open>Bet E F F' \<or> Bet E F' F\<close> by auto
            moreover 
            {
              assume "Bet C D D'" and "Bet E F F'"
              have "F \<noteq> E" 
                using \<open>E \<noteq> F\<close> by blast
              moreover have "F'' \<noteq> E" 
                using \<open>A \<noteq> B\<close> \<open>Parallelogram A B F'' E\<close> plg_not_comm_R1 by blast
              moreover have "Bet E F' F''"
              proof (rule plg_plg_bet [where ?A="C" and ?B="D" and ?B'="D'"])
                show "Parallelogram C D F' E" 
                  by (simp add: \<open>Parallelogram C D F' E\<close>)
                show "Bet C D D'" 
                  by (simp add: \<open>Bet C D D'\<close>)
                show "Parallelogram C D' F'' E" 
                  by (simp add: \<open>Parallelogram C D' F'' E\<close>)
              qed
              have "Bet E F F''" 
                using between_exchange4 [where ?C = "F'"] \<open>Bet E F F'\<close> \<open>Bet E F' F''\<close> by blast
              hence "Bet E F F'' \<or> Bet E F'' F" 
                by blast
              ultimately have ?thesis
                by (simp add: Out_def)
            }
            moreover {
              assume "Bet C D D'" and "Bet E F' F"
              have "F \<noteq> E" 
                using \<open>E \<noteq> F\<close> by blast
              moreover have "F'' \<noteq> E" 
                using \<open>A \<noteq> B\<close> \<open>Parallelogram A B F'' E\<close> plg_not_comm_R1 by blast
              moreover
              have "Bet E F' F''" 
                using plg_plg_bet [where ?A="C" and ?B="D" and ?B'="D'"]
                  \<open>Parallelogram C D F' E\<close> \<open>Bet C D D'\<close> \<open>Parallelogram C D' F'' E\<close> by blast
              have "Bet E F F'' \<or> Bet E F'' F" 
                using l5_1 [where ?B = "F'"] \<open>E \<noteq> F'\<close> \<open>Bet E F' F\<close> \<open>Bet E F' F''\<close> by blast
              ultimately have ?thesis
                using Out_def by blast
            }
            moreover 
            {
              assume "Bet C D' D" and "Bet E F F'" 
              have "F \<noteq> E" 
                using \<open>E \<noteq> F\<close> by blast
              moreover have "F'' \<noteq> E" 
                using \<open>A \<noteq> B\<close> \<open>Parallelogram A B F'' E\<close> plg_not_comm_R1 by blast
              moreover have "Bet E F F'' \<or> Bet E F'' F" 
              proof (rule l5_3 [where ?D = "F'"])
                show "Bet E F F'" 
                  by (simp add: \<open>Bet E F F'\<close>)
                show "Bet E F'' F'" 
                  using plg_plg_bet [where ?A="C" and ?B="D'" and ?B'="D"]
                    \<open>Parallelogram C D' F'' E\<close> \<open>Bet C D' D\<close> \<open>Parallelogram C D F' E\<close> by blast
              qed
              ultimately have ?thesis 
                by (simp add: Out_def)
            }
            moreover {
              assume "Bet C D' D" and "Bet E F' F"
              have "F \<noteq> E" 
                using \<open>E \<noteq> F\<close> by blast
              moreover have "F'' \<noteq> E" 
                using \<open>A \<noteq> B\<close> \<open>Parallelogram A B F'' E\<close> plg_not_comm_R1 by blast
              moreover have "Bet E F F'' \<or> Bet E F'' F" 
              proof -
                have "Bet E F'' F'" 
                  using plg_plg_bet [where ?A="C" and ?B="D'" and ?B'="D"] 
                    \<open>Bet C D' D\<close> \<open>Parallelogram C D F' E\<close> \<open>Parallelogram C D' F'' E\<close> by blast
                thus ?thesis 
                  using \<open>Bet E F' F\<close> between_exchange4 by blast
              qed
              ultimately have ?thesis 
                by (simp add: Out_def)
            }
            ultimately have ?thesis 
              by blast
          }
          ultimately show ?thesis 
            by blast
        qed
        hence "\<exists> D'0. E Out F D'0 \<and> A B EqV E D'0"  
          using \<open>A B EqV E F''\<close> by blast
      }
      ultimately have "\<exists> D'0. E Out F D'0 \<and> A B EqV E D'0"  
        by blast
    }
    hence ?thesis 
      using SameDir_def calculation(1) calculation(2) by presburger
  }
  thus ?thesis 
    using calculation(1) calculation(2) by blast
qed

lemma same_dir_comm:
  assumes "A B SameDir C D" 
  shows "B A SameDir D C" 
proof -
  have "A = B \<and> C = D \<longrightarrow> ?thesis" 
    using assms by force
  moreover {
    assume "\<exists> D'. C Out D D' \<and> A B EqV C D'"
    then obtain D' where "C Out D D'" and "A B EqV C D'" 
      by blast
    hence H0: "Bet C D D' \<or> Bet C D' D" 
      using Out_def by simp
    have "A \<noteq> B" 
      using \<open>\<exists>D'. C Out D D' \<and> A B EqV C D'\<close> l6_3_1 null_vector by blast
    obtain C' where "B A EqV D C'" 
      using vector_construction by blast
    have "D Out C C'" 
    proof -
      have "C \<noteq> D" 
        using \<open>C Out D D'\<close> l6_3_1 by blast
      moreover have "C' \<noteq> D" 
        using \<open>A \<noteq> B\<close> \<open>B A EqV D C'\<close> eqv_sym null_vector by blast
      moreover 
      have "Bet D C C' \<or> Bet D C' C"
      proof -
        {
          assume "Parallelogram A B D' C"
          hence "Parallelogram C D' D C' \<or> (C = D' \<and> B = A \<and> C' = D \<and> C = C')" 
            by (metis EqV_def Plg_perm \<open>A \<noteq> B\<close> \<open>B A EqV D C'\<close> plg_pseudo_trans)
          moreover 
          {
            assume "Parallelogram C D' D C'"
            have "ParallelogramFlat C D' D C'" 
              by (meson Col_def Out_def \<open>C Out D D'\<close> \<open>Parallelogram C D' D C'\<close>
                  between_symmetry plg_col_plgf)
            hence H1: "Col C D' D \<and> Col C D' C' \<and> Cong C D' D C' \<and> 
                       Cong C C' D D' \<and> (C \<noteq> D \<or> D' \<noteq> C')"
              using ParallelogramFlat_def by simp
            have "Col D' C C'" 
              using H1 col_permutation_4 by blast
            have "Cong D' C D C'" 
              using H1 not_cong_2134 by blast
            have "Cong D' D C C'" 
              using H1 not_cong_3421 by blast
            hence "Bet D' D C \<longrightarrow> ?thesis"
              using col_cong2_bet1 [where ?A = "D'"] \<open>Col D' C C'\<close> \<open>Cong D' C D C'\<close> by blast
            moreover {
              assume "Bet C D' D"
              {
                assume "Parallelogram A B D' C"
                {
                  assume "Parallelogram B A C' D"
                  have "C = C' \<longrightarrow> ?thesis " 
                    using between_trivial by presburger
                  moreover {
                    assume "C \<noteq> C'"
                    have "Parallelogram C D' D C' \<or> (C = D' \<and> B = A \<and> C' = D \<and> C = C')" 
                      using \<open>Parallelogram C D' D C'\<close> by blast
                    moreover {
                      assume "Parallelogram C D' D C'"
                      have "ParallelogramFlat C D' D C'" 
                        by (simp add: \<open>ParallelogramFlat C D' D C'\<close>)
                      moreover have "ParallelogramStrict C D' D C' \<longrightarrow> ?thesis" 
                        using H1 col_not_plgs by blast
                      moreover have "ParallelogramFlat C D' D C' \<longrightarrow> Bet D C' C" 
                        by (metis \<open>Bet C D' D\<close> \<open>Cong D' C D C'\<close> \<open>Cong D' D C C'\<close> 
                            \<open>Parallelogram C D' D C'\<close> bet_cong_eq between_symmetry 
                            calculation(2) ncol134_plg__plgs third_point)
                      ultimately have ?thesis
                        by blast
                    }
                    moreover have "(C = D' \<and> B = A \<and> C' = D \<and> C = C') \<longrightarrow> ?thesis" 
                      using \<open>A \<noteq> B\<close> by auto
                    ultimately have ?thesis 
                      by blast
                  }
                  ultimately have ?thesis
                    by blast
                }
                moreover have "B = A \<and> D = C' \<longrightarrow> ?thesis" 
                  using \<open>A \<noteq> B\<close> by blast
                ultimately have ?thesis 
                  using EqV_def \<open>B A EqV D C'\<close> by presburger
              }
              moreover have "A = B \<and> C = D' \<longrightarrow> ?thesis" 
                using \<open>A \<noteq> B\<close> by blast
              ultimately have ?thesis 
                using \<open>Parallelogram A B D' C\<close> by blast
            }
            ultimately have ?thesis 
              using Bet_cases H0 by blast
          }
          moreover have  "(C = D' \<and> B = A \<and> C' = D \<and> C = C') \<longrightarrow> ?thesis" 
            using \<open>A \<noteq> B\<close> by auto
          ultimately have ?thesis 
            by blast
        }
        moreover have "A = B \<and> C = D' \<longrightarrow> ?thesis"         
          using \<open>A \<noteq> B\<close> by auto
        ultimately show ?thesis
          using EqV_def \<open>A B EqV C D'\<close> by force
      qed
      hence "Bet D C C' \<or> Bet D C' C" 
        by blast
      ultimately show ?thesis 
        by (simp add: Out_def)
    qed
    hence "\<exists> D'0. D Out C D'0 \<and> B A EqV D D'0" 
      using \<open>B A EqV D C'\<close> by blast
  }
  hence "(\<exists> D'. C Out D D' \<and> A B EqV C D') \<longrightarrow> ?thesis" 
    by (simp add: SameDir_def)
  ultimately show ?thesis
    using SameDir_def assms by auto
qed

lemma bet_same_dir1:
  assumes "A \<noteq> B" and
    (*"B \<noteq> C" and*)
    "Bet A B C"
  shows "A B SameDir A C" 
  by (metis Out_def SameDir_def assms(1) assms(2) bet_neq21__neq eqv_refl)

lemma bet_same_dir2: 
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Bet A B C"
  shows "A B SameDir B C" 
  by (metis Bet_cases assms(1) assms(2) assms(3) bet_same_dir1 same_dir_comm 
      same_dir_sym same_dir_trans)

lemma plg_opp_dir:
  assumes "Parallelogram A B C D"
  shows "A B SameDir D C" 
  by (metis EqV_def SameDir_def assms between_equality not_bet_distincts 
      not_col_distincts not_out_bet plg_not_comm)

lemma same_dir_dec:
  shows "A B SameDir C D \<or> \<not> A B SameDir C D" 
  by blast

lemma same_or_opp_dir: 
  assumes "A B Par C D"
  shows "A B SameDir C D \<or> A B OppDir C D" 
proof (cases "A B SameDir C D")
  case True
  thus ?thesis
    by blast
next
  case False
  hence "\<not> A B SameDir C D" 
    by blast
  obtain C' where "A B EqV D C'" 
    using vector_construction by fastforce
  have "D Out C C'" 
  proof (cases "B = C'")
    case True
    hence "B = C'" 
      by blast
    have "Parallelogram A B B D \<longrightarrow> ?thesis" 
    proof -
      {
        assume "ParallelogramStrict A B B D"
        hence "Col B D B" 
          by (simp add: col_trivial_3)
        hence False 
          using \<open>ParallelogramStrict A B B D\<close> plgs_diff by blast
      }
      hence "ParallelogramStrict A B B D \<longrightarrow> ?thesis" 
        by blast
      moreover 
      {
        assume "ParallelogramFlat A B B D"
        hence "D = A \<and> B \<noteq> D" 
          using plgf_permut plgf_trivial_neq by blast
        hence ?thesis 
          by (metis False True \<open>\<And>thesis. (\<And>C'. A B EqV D C' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
              assms bet_same_dir2 eqv_par not_col_distincts not_out_bet par_distincts 
              parallel_uniqueness same_dir_sym vector_uniqueness)
      }
      ultimately show ?thesis
        using Parallelogram_def by blast
    qed
    moreover have "A = B \<and> D = B \<longrightarrow> ?thesis"
      using assms par_neq1 by blast
    ultimately show ?thesis 
      using EqV_def True \<open>A B EqV D C'\<close> by blast
  next
    case False
    {
      assume "Parallelogram A B C' D"
      have "Col C' C D \<and> Col D C D" 
        by (metis Par_cases \<open>A B EqV D C'\<close> assms eqv_par par_id_4 par_neq1 
            par_not_par parallel_uniqueness)
      hence "Col C' C D" 
        by blast
      have "C \<noteq> D" 
        using assms par_distinct by auto
      moreover have "C' \<noteq> D" 
        using \<open>Parallelogram A B C' D\<close> assms par_neq1 plg_not_comm_R1 by blast
      moreover have "Bet D C C' \<or> Bet D C' C" 
      proof -
        have "Bet C' C D \<longrightarrow> ?thesis" 
          using between_symmetry by blast
        moreover 
        {
          assume "Bet C D C'"
          have "A B SameDir D C'" 
            by (simp add: \<open>Parallelogram A B C' D\<close> plg_opp_dir)
          moreover have "C D SameDir D C'" 
            using \<open>Bet C D C'\<close> \<open>C \<noteq> D\<close> \<open>C' \<noteq> D\<close> bet_same_dir2 by force
          ultimately have "A B SameDir C D" 
            by (meson same_dir_sym same_dir_trans)
          hence False 
            using \<open>\<not> A B SameDir C D\<close> by blast
        }
        ultimately show ?thesis 
          using Col_def \<open>Col C' C D\<close> by blast
      qed
      ultimately have ?thesis 
        by (simp add: Out_def)
    }
    moreover have "A = B \<and> D = C' \<longrightarrow> ?thesis" 
      using assms par_distinct by blast
    ultimately show ?thesis 
      using EqV_def \<open>A B EqV D C'\<close> by blast
  qed
  hence "\<exists> D'. D Out C D' \<and> A B EqV D D'" 
    using \<open>A B EqV D C'\<close> by blast
  hence "A B SameDir D C" 
    by (simp add: SameDir_def)
  hence "A B OppDir C D" 
    by (simp add: OppDir_def)
  thus ?thesis 
    by blast
qed

lemma same_dir_id:
  assumes "A B SameDir B A"
  shows "A = B" 
  using assms bet_neq32__neq same_dir_ts by blast

lemma opp_dir_id: 
  assumes "A B OppDir A B"
  shows "A = B" 
  using OppDir_def assms same_dir_id by blast

lemma same_dir_to_null:
  assumes "A B SameDir C D" and
    "A B SameDir D C"
  shows "A = B \<and> C = D" 
  by (meson assms(1) assms(2) same_dir_comm same_dir_id same_dir_sym same_dir_trans)

lemma opp_dir_to_null: 
  assumes "A B OppDir C D" and
    "A B OppDir D C"
  shows "A = B \<and> C = D" 
  using OppDir_def assms(1) assms(2) same_dir_to_null by auto

lemma same_not_opp_dir: 
  assumes "A \<noteq> B" and
    "A B SameDir C D"
  shows "\<not> A B OppDir C D" 
  using OppDir_def assms(1) assms(2) same_dir_to_null by blast

lemma opp_not_same_dir: 
  assumes "A \<noteq> B" and
    "A B OppDir C D" 
  shows "\<not> A B SameDir C D" 
  using assms(1) assms(2) same_not_opp_dir by force

lemma vector_same_dir_cong: 
  assumes "A \<noteq> B" and
    "C \<noteq> D"
  shows "\<exists> X Y. A B SameDir X Y \<and> Cong X Y C D" 
  by (metis assms(1) assms(2) bet_same_dir2 cong_diff_3 segment_construction)

end

subsubsection "Projections"
  (* Gabriel Braun March 2013 *)
context Tarski_Euclidean_2D

begin

lemma (in Tarski_neutral_dimensionless) project_id:
  assumes "P P' Proj A B X Y" and
    "Col A B P"
  shows "P = P'" 
proof -
  {
    assume "P P' Par X Y"
    have "P' = A \<longrightarrow> A B Par X Y" 
      by (metis Proj_def \<open>P P' Par X Y\<close> assms(1) assms(2) not_col_permutation_5 
          par_col_par_2 par_left_comm)
    moreover 
    {
      assume "P' \<noteq> A"
      have "Col P' P A" 
        by (metis Proj_def assms(1) assms(2) col3 not_col_distincts)
      moreover have "P' P Par X Y" 
        by (simp add: \<open>P P' Par X Y\<close> par_left_comm)
      ultimately have "A P' Par X Y" 
        using \<open>P' \<noteq> A\<close> par_col_par_2 par_left_comm by presburger
      hence "A B Par X Y" 
        by (metis Proj_def assms(1) not_col_permutation_5 par_col_par_2)
    }
    ultimately have "A B Par X Y" 
      by blast
    hence False     
      using Proj_def assms(1) by force
  }
  thus ?thesis 
    using Proj_def assms(1) by force
qed

lemma (in Tarski_neutral_dimensionless) project_not_id:
  assumes "P P' Proj A B X Y" and
    "\<not> Col A B P"
  shows "P \<noteq> P'" 
  using Proj_def assms(1) assms(2) by force

lemma (in Tarski_neutral_dimensionless) project_col: 
  assumes "P P Proj A B X Y"
  shows "Col A B P" 
  using assms project_not_id by blast

lemma (in Tarski_neutral_dimensionless) project_not_col: 
  assumes "P P' Proj A B X Y" and
    "P \<noteq> P'"
  shows "\<not> Col A B P" 
  using assms(1) assms(2) project_id by blast

lemma (in Tarski_Euclidean) project_par: 
  assumes "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "P Q Par X Y"
  shows "P' = Q'" 
proof -
  {
    assume "P P' Par X Y"
    hence "Col P P P' \<and> Col Q P P'" 
      using parallel_uniqueness assms(3) not_par_one_not_par par_id_5 by blast
    hence "Col Q P P'" 
      by simp
    {
      assume "Q Q' Par X Y"
      have "Col P Q Q' \<and> Col Q Q Q'" 
        using parallel_uniqueness 
        by (meson \<open>Col Q P P'\<close> \<open>P P' Par X Y\<close> \<open>Q Q' Par X Y\<close> col_trivial_1 par_symmetry)
      hence "Col P Q Q'" 
        by simp
      have ?thesis 
        by (metis Proj_def \<open>Col P Q Q'\<close> \<open>Col Q P P'\<close> \<open>P P' Par X Y\<close> assms(1) 
            assms(2) assms(3) col_permutation_4 l6_21 par_distincts project_id)
    }
    moreover have "Q = Q' \<longrightarrow> ?thesis" 
      using l6_21 by (metis NCol_perm Proj_def \<open>Col Q P P'\<close> 
          \<open>P P' Par X Y\<close> assms(1) assms(2) par_distincts par_id_5 
          par_reflexivity project_not_col)
    ultimately have ?thesis 
      using Proj_def assms(2) by force
  }
  moreover 
  {
    assume "P = P'"
    have "A \<noteq> B" 
      using Proj_def assms(2) by force
    have "X \<noteq> Y" 
      using assms(3) par_distincts by blast
    have "\<not> A B Par X Y" 
      using Proj_def assms(2) by presburger
    have "Col A B Q'" 
      using Proj_def assms(2) by force
    {
      assume "Q Q' Par X Y" 
      hence "Q \<noteq> Q'" 
        using par_distinct by presburger
      have "Col P Q Q' \<and> Col Q Q Q'" 
        using parallel_uniqueness 
        by (metis \<open>Q Q' Par X Y\<close> assms(3) not_par_one_not_par par_id_5)
      hence "Col P Q Q'" 
        by simp
      have "P' = Q'" 
      proof (rule l6_21 [where ?A = "A" and ?B = "B" and ?C = "Q" and ?D = "P"])
        show "\<not> Col A B Q" 
          using \<open>Q \<noteq> Q'\<close> assms(2) project_id by blast
        show "Q \<noteq> P" 
          using assms(3) par_neq1 by blast
        show "Col A B P'" 
          using Proj_def assms(1) by force
        show "Col A B Q'" 
          by (simp add: \<open>Col A B Q'\<close>)
        show "Col Q P P'" 
          using \<open>P = P'\<close> not_col_distincts by blast
        show "Col Q P Q'" 
          using \<open>Col P Q Q'\<close> not_col_permutation_4 by blast
      qed
    }
    moreover 
    {
      assume "Q = Q'"
      have "A = P \<longrightarrow> A B Par X Y" 
        by (metis \<open>A \<noteq> B\<close> \<open>Col A B Q'\<close> \<open>Q = Q'\<close> assms(3) col3 
            col_trivial_2 col_trivial_3 par_col_par_2)
      moreover {
        assume "A \<noteq> P"
        have "A B Par X Y" 
        proof (rule par_col_par_2 [where ?B = "Q"])
          show "A \<noteq> B" 
            by (simp add: \<open>A \<noteq> B\<close>)
          show "Col A Q B" 
            using \<open>Col A B Q'\<close> \<open>Q = Q'\<close> not_col_permutation_5 by blast
          have "A P Par X Y" 
            using \<open>A \<noteq> B\<close> \<open>Col A B Q'\<close> \<open>P = P'\<close> \<open>Q = Q'\<close> \<open>\<not> A B Par X Y\<close> assms(1) 
              assms(3) par_col2_par_bis par_symmetry project_not_id by blast
          thus "A Q Par X Y" 
            by (metis Proj_def \<open>P = P'\<close> assms(1) par_col_par par_distinct 
                par_reflexivity postulate_of_transitivity_of_parallelism_def 
                postulate_of_transitivity_of_parallelism_thm)
        qed
      }
      ultimately have "A B Par X Y" 
        by blast
      hence False 
        by (simp add: \<open>\<not> A B Par X Y\<close>)
    }
    ultimately have "P' = Q'" 
      using Proj_def assms(2) by auto
  }
  ultimately show ?thesis
    using Proj_def assms(1) by force
qed

lemma (in Tarski_Euclidean) ker_col: 
  assumes "P P' Proj A B X Y" and
    "Q P' Proj A B X Y" 
  shows "Col P Q P'" 
  by (metis Par_perm Proj_def assms(1) assms(2) not_col_distincts not_par_one_not_par par_id_2)

lemma (in Tarski_Euclidean) ker_par: 
  assumes "P \<noteq> Q" and
    "P P' Proj A B X Y" and
    "Q P' Proj A B X Y"
  shows "P Q Par X Y"
proof -
  have "Col P Q P'" 
    using assms(2) assms(3) ker_col by blast
  {
    assume "P P' Par X Y" 
    hence ?thesis 
      by (metis NCol_cases assms(1) assms(2) assms(3) ker_col par_col_par_2)
  }
  moreover have "P = P' \<longrightarrow> ?thesis" 
    by (metis Proj_def assms(1) assms(3) par_left_comm)
  ultimately show ?thesis
    using Proj_def assms(2) by force
qed

lemma (in Tarski_Euclidean) project_uniqueness: 
  assumes "P P' Proj A B X Y" and
    "P Q' Proj A B X Y"
  shows "P' = Q'" 
  by (metis Proj_def assms(1) assms(2) colx not_par_one_not_par par_id_2 project_id)

lemma (in Tarski_Euclidean_2D) project_existence:
  assumes "X \<noteq> Y" and
    "A \<noteq> B" and
    "\<not> X Y Par A B" 
  shows "\<exists> P'. P P' Proj A B X Y" 
proof -
  obtain x x0 where "x \<noteq> x0" and "X Y Par x x0" and "Col P x x0" 
    by (metis assms(1) col_trivial_1 par_neq2 parallel_existence1)
  have "\<not> x x0 Par A B" 
    using \<open>X Y Par x x0\<close> assms(3) par_trans by blast
  then obtain P' where "Col P' x x0" and "Col P' A B" 
    using not_par_inter_exists by blast
  hence "P P' Proj A B X Y" 
    by (metis (full_types) Proj_def \<open>Col P x x0\<close> 
        \<open>X Y Par x x0\<close> \<open>x \<noteq> x0\<close> assms(1) assms(2) assms(3) col_par 
        l6_16_1 not_col_permutation_2 par_not_par par_symmetry)
  thus ?thesis 
    by blast
qed

lemma (in Tarski_Euclidean) project_col_eq:
  assumes "P \<noteq> P'" and
    "Col P Q P'" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y"
  shows "P' = Q'" 
  by (metis Proj_def assms(1) assms(2) assms(3) assms(4) not_par_not_col 
      par_not_par project_par project_uniqueness)

lemma (in Tarski_Euclidean) par_col_project:
  assumes "A \<noteq> B" and
    "\<not> A B Par X Y" and
    "P P' Par X Y" and
    "Col A B P'"
  shows "P P' Proj A B X Y" 
  using Proj_def assms(1) assms(2) assms(3) assms(4) par_neq2 by presburger

lemma project_preserves_bet:
  assumes "Bet P Q R" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "R R' Proj A B X Y" 
  shows "Bet P' Q' R'" 
proof -
  have "Col P' Q' R'" 
    by (metis Proj_def assms(2) assms(3) assms(4) col3)
  have "P = Q \<longrightarrow> ?thesis" 
    using assms(2) assms(3) not_bet_distincts project_uniqueness by blast
  moreover 
  {
    assume "P \<noteq> Q"
    have "R = Q \<longrightarrow> ?thesis " 
      using assms(3) assms(4) not_bet_distincts project_uniqueness by blast
    moreover 
    {
      assume "R \<noteq> Q"
      have "P' = Q' \<longrightarrow> ?thesis" 
        by (simp add: between_trivial2)
      moreover 
      {
        assume "P' \<noteq> Q'"
        have "R' = Q' \<longrightarrow> ?thesis" 
          by (simp add: between_trivial)
        moreover 
        {
          assume "R' \<noteq> Q'"
          {
            assume "P P' Par X Y"
            {
              assume "Q Q' Par  X Y"
              hence "P P' Par Q Q'" 
                using \<open>P P' Par X Y\<close> not_par_one_not_par by blast
              hence "Q Q' ParStrict P P'" 
                by (metis Par_cases \<open>P P' Par X Y\<close> \<open>P \<noteq> Q\<close> \<open>P' \<noteq> Q'\<close> 
                    all_one_side_par_strict assms(2) assms(3) not_strict_par 
                    par_col_par_2 par_neq1 par_not_col_strict project_par)
              hence "Q Q' OS P P'" 
                by (simp add: l12_6)
              {
                assume "R R' Par X Y"
                hence "R R' Par Q Q'" 
                  using \<open>Q Q' Par X Y\<close> not_par_one_not_par by blast
                hence "Q Q' ParStrict R R'" 
                  by (metis Par_cases \<open>Col P' Q' R'\<close> \<open>Q Q' ParStrict P P'\<close> \<open>R' \<noteq> Q'\<close> 
                      col_trivial_2 l6_16_1 par_not_col_strict par_strict_not_col_4)
                hence "Q Q' OS R R'" 
                  by (simp add: l12_6)
                hence "Q Q' TS P R" 
                  using \<open>Q Q' ParStrict P P'\<close> assms(1) bet__ts os_distincts
                    par_strict_not_col_1 by force
                hence "Q Q' TS P' R'" 
                  using \<open>Q Q' OS P P'\<close> \<open>Q Q' OS R R'\<close> l9_2 l9_8_2 by blast
                then obtain QQ where "Col QQ Q Q'" and "Bet P' QQ R'" 
                  using TS_def by fastforce
                hence "QQ = Q'" 
                  by (meson \<open>Col P' Q' R'\<close> \<open>Q Q' TS P' R'\<close> bet_col 
                      col_permutation_5 colx not_col_permutation_4 ts__ncol)
                hence ?thesis 
                  using \<open>Bet P' QQ R'\<close> by blast
              }
              moreover 
              {
                assume "R = R'"
                have "Q Q' TS P' R" 
                  by (metis \<open>Q Q' OS P P'\<close> \<open>Q Q' ParStrict P P'\<close> \<open>R \<noteq> Q\<close> 
                      assms(1) bet__ts l9_8_2 par_strict_not_col_1)
                then obtain QQ where "Col QQ Q Q'" and "Bet P' QQ R" 
                  using TS_def by blast
                hence "Col P' QQ R" 
                  by (simp add: Col_def)
                have "QQ = Q'" 
                proof (rule l6_21 [where ?A= "Q" and ?B="Q'" and ?C="P'" and ?D="R"])
                  show "\<not> Col Q Q' P'" 
                    using \<open>Q Q' ParStrict P P'\<close> par_strict_not_col_4 by auto
                  show "P' \<noteq> R" 
                    using \<open>Q Q' TS P' R\<close> ts_distincts by blast
                  show "Col Q Q' QQ" 
                    using \<open>Col QQ Q Q'\<close> not_col_permutation_2 by blast
                  show "Col Q Q' Q'" 
                    using not_col_distincts by blast
                  show "Col P' R QQ" 
                    using \<open>Col P' QQ R\<close> not_col_permutation_5 by blast
                  show "Col P' R Q'" 
                    by (simp add: \<open>Col P' Q' R'\<close> \<open>R = R'\<close> col_permutation_5)
                qed
                hence ?thesis 
                  using \<open>Bet P' QQ R\<close> \<open>R = R'\<close> by auto
              }
              ultimately have ?thesis 
                using Proj_def assms(4) by force
            }
            moreover 
            {
              assume "Q = Q'"
              {
                assume "R R' Par X Y"
                then obtain Qx Qy where "Qx \<noteq> Qy" and "X Y Par Qx Qy" and "Col Q Qx Qy" 
                  using \<open>P P' Par X Y\<close> par_neq2 parallel_existence by blast
                hence "Qx Qy Par P P'" 
                  using Par_perm \<open>P P' Par X Y\<close> par_trans by blast
                hence "Qx Qy ParStrict P P'" 
                  by (metis NCol_perm Par_perm Par_strict_cases \<open>Col Q Qx Qy\<close>
                      \<open>P P' Par X Y\<close> \<open>P \<noteq> Q\<close> \<open>P' \<noteq> Q'\<close> assms(2) assms(3) col_trivial_3 
                      par_col2_par par_not_col_strict project_par)
                hence "Qx Qy OS P P'" 
                  using l12_6 by auto
                have "Qx Qy Par R R'" 
                  using \<open>P P' Par X Y\<close> \<open>Qx Qy Par P P'\<close> \<open>R R' Par X Y\<close> 
                    not_par_one_not_par by blast
                hence "Qx Qy ParStrict R R'" 
                  by (metis Par_def \<open>Col Q Qx Qy\<close> \<open>R R' Par X Y\<close> \<open>R \<noteq> Q\<close> \<open>R' \<noteq> Q'\<close> 
                      \<open>X Y Par Qx Qy\<close> assms(3) assms(4) parallel_uniqueness 
                      postulate_of_transitivity_of_parallelism_def 
                      postulate_of_transitivity_of_parallelism_thm project_par) (* 2.0 s *)
                hence "Qx Qy OS R R'" 
                  using l12_6 by force
                hence "Qx Qy TS P R" 
                  using OS_def TS_def \<open>Col Q Qx Qy\<close> \<open>Qx Qy OS P P'\<close> assms(1) by auto
                hence "Qx Qy TS P' R'" 
                  using \<open>Qx Qy OS P P'\<close> \<open>Qx Qy OS R R'\<close> l9_2 l9_8_2 by blast
                then obtain QQ where "Col QQ Qx Qy" and "Bet P' QQ R'" 
                  using TS_def by blast
                have "QQ = Q" 
                proof (rule l6_21 [where ?A="Qx" and ?B="Qy" and ?C="P'" and ?D="R'"])
                  show "\<not> Col Qx Qy P'" 
                    using \<open>Qx Qy OS P P'\<close> col124__nos by blast
                  show "P' \<noteq> R'" 
                    using \<open>Qx Qy TS P' R'\<close> not_two_sides_id by force
                  show "Col Qx Qy QQ" 
                    using Col_cases \<open>Col QQ Qx Qy\<close> by blast
                  show "Col Qx Qy Q" 
                    using \<open>Col Q Qx Qy\<close> not_col_permutation_2 by blast
                  show "Col P' R' QQ" 
                    using \<open>Bet P' QQ R'\<close> bet_col not_col_permutation_5 by blast
                  show "Col P' R' Q" 
                    by (simp add: \<open>Col P' Q' R'\<close> \<open>Q = Q'\<close> col_permutation_5)
                qed
                hence ?thesis 
                  using \<open>Bet P' QQ R'\<close> \<open>Q = Q'\<close> by auto
              }
              moreover 
              have "\<not> Col A B P" 
                using \<open>P P' Par X Y\<close> assms(2) par_neq1 project_not_col by auto
              {
                assume "R = R'"
                hence "Col A B P" 
                  by (metis Proj_def \<open>Q = Q'\<close> \<open>R \<noteq> Q\<close> assms(1) assms(3) assms(4) 
                      bet_col bet_col1 l6_21)
                hence False 
                  using \<open>\<not> Col A B P\<close> by blast
              }
              ultimately have ?thesis 
                using Proj_def assms(4) by force
            }
            ultimately have ?thesis
              using Proj_def assms(3) by force
          }
          moreover 
          {
            assume "P = P'"
            {
              assume "Q Q' Par X Y"
              {
                assume "R R' Par X Y"
                hence "Q Q' Par R R'" 
                  using \<open>Q Q' Par X Y\<close> not_par_one_not_par by blast
                hence "Q Q' ParStrict R R'" 
                  by (metis Par_def \<open>R R' Par X Y\<close> \<open>R \<noteq> Q\<close> \<open>R' \<noteq> Q'\<close> assms(3) 
                      assms(4) ker_col postulate_of_transitivity_of_parallelism_def 
                      postulate_of_transitivity_of_parallelism_thm project_par)
                hence "Q Q' OS R R'" 
                  using l12_6 by blast
                hence "Q Q' TS P R'" 
                  by (metis \<open>P \<noteq> Q\<close> assms(1) bet__ts between_symmetry l9_2 l9_8_2 
                      one_side_not_col123)
                then obtain QQ where "Col QQ Q Q'" and "Bet P QQ R'" 
                  using TS_def by blast
                have "QQ = Q'" 
                proof (rule l6_21 [where ?A="Q" and ?B="Q'" and ?C="P" and ?D="R'"])
                  show "\<not> Col Q Q' P" 
                    using TS_def \<open>Q Q' TS P R'\<close> col_permutation_2 by blast
                  show "P \<noteq> R'" 
                    using \<open>Q Q' TS P R'\<close> ts_distincts by blast
                  show "Col Q Q' QQ" 
                    using Col_cases \<open>Col QQ Q Q'\<close> by blast
                  show "Col Q Q' Q'" 
                    using not_col_distincts by blast
                  show "Col P R' QQ" 
                    using Bet_cases Col_def \<open>Bet P QQ R'\<close> by blast
                  show "Col P R' Q'" 
                    using Col_cases \<open>Col P' Q' R'\<close> \<open>P = P'\<close> by auto
                qed
                hence ?thesis 
                  using \<open>Bet P QQ R'\<close> \<open>P = P'\<close> by blast
              }
              moreover have "R = R' \<longrightarrow> ?thesis" 
                by (metis \<open>Col P' Q' R'\<close> \<open>P = P'\<close> \<open>R' \<noteq> Q'\<close> assms(1) assms(3) assms(4) 
                    not_col_permutation_2 or_bet_out out_bet_out_2 out_col project_col_eq)
              ultimately have ?thesis 
                using Proj_def assms(4) by force
            }
            moreover have "Q = Q' \<longrightarrow> ?thesis" 
              by (metis Proj_def \<open>P = P'\<close> \<open>P' \<noteq> Q'\<close> assms(1) assms(2) assms(3) 
                  assms(4) bet_col colx project_not_col)
            ultimately have ?thesis 
              using Proj_def assms(3) by force
          }
          ultimately have ?thesis 
            using Proj_def assms(2) by force
        }
        ultimately have ?thesis 
          by blast
      }
      ultimately have ?thesis 
        by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma triangle_par:
  assumes "\<not> Col A B C" and
    "A B Par A' B'" and
    "B C Par B' C'" and 
    "A C Par A' C'" 
  shows "A B C CongA A' B' C'" 
proof -
  obtain M where "M Midpoint B B'" 
    using MidR_uniq_aux by blast
  obtain A'' where "Bet A' M A''" and "Cong M A'' A' M"
    using segment_construction by blast
  obtain C'' where "Bet C' M C''" and "Cong M C'' C' M" 
    using segment_construction by blast
  have "M Midpoint A' A''" 
    using \<open>Bet A' M A''\<close> \<open>Cong M A'' A' M\<close> midpoint_def not_cong_3412 by blast
  have "M Midpoint C' C''" 
    using \<open>Bet C' M C''\<close> \<open>Cong M C'' C' M\<close> midpoint_def not_cong_3412 by blast
  have "A' \<noteq> B'" 
    using assms(2) par_distinct by blast
  have "C' \<noteq> B'" 
    using assms(3) par_distinct by blast
  have "B' C' Par B C''" 
    using \<open>C' \<noteq> B'\<close> \<open>M Midpoint B B'\<close> \<open>M Midpoint C' C''\<close> mid_par_cong2 
      par_comm by presburger
  hence "Col B B C \<and> Col C'' B C" 
    using assms(3) not_col_distincts not_par_one_not_par par_id_1 par_symmetry by blast
  hence "Col C'' B C" 
    by blast
  have "B' A' Par B A''" 
    using \<open>A' \<noteq> B'\<close> \<open>M Midpoint A' A''\<close> \<open>M Midpoint B B'\<close> mid_par_cong2
      par_comm by presburger
  hence "Col A'' B A" 
    by (meson assms(2) par_comm par_id_5 par_not_par)
  have "A' B' C' CongA A'' B C''" 
    by (meson \<open>A' \<noteq> B'\<close> \<open>C' \<noteq> B'\<close> \<open>M Midpoint A' A''\<close> \<open>M Midpoint B B'\<close> 
        \<open>M Midpoint C' C''\<close> l7_2 symmetry_preserves_conga)
  have "A B C CongA A'' B C''"
  proof -
    have "B \<noteq> A''" 
      using \<open>B' A' Par B A''\<close> par_distinct by auto
    have "B \<noteq> C''" 
      using \<open>B' C' Par B C''\<close> par_distinct by auto
    have "A \<noteq> B" 
      using \<open>Col B B C \<and> Col C'' B C\<close> assms(1) by blast
    have "C \<noteq> B" 
      using assms(3) par_distinct by auto
    have "A C Par A'' C''" 
      using \<open>M Midpoint A' A''\<close> \<open>M Midpoint C' C''\<close> assms(4) l12_17 
        par_neq2 par_not_par by blast
    {
      assume "Bet C'' B C"
      have "A C ParStrict A'' C''" 
        by (metis Col_perm \<open>A C Par A'' C''\<close> \<open>Bet C'' B C\<close> \<open>Col C'' B C\<close> assms(1) 
            between_identity col3 col_trivial_2 par_not_col_strict)
      have "Bet A'' B A \<longrightarrow> ?thesis" 
        by (metis Bet_cases \<open>A \<noteq> B\<close> \<open>B \<noteq> A''\<close> \<open>B \<noteq> C''\<close> \<open>Bet C'' B C\<close> \<open>C \<noteq> B\<close> l11_14)
      moreover {
        assume "Bet B A A'' \<or> Bet A A'' B"
        have "A = A'' \<longrightarrow> False" 
          using \<open>A C ParStrict A'' C''\<close> not_par_strict_id by blast
        moreover {
          assume "A \<noteq> A''"
          {
            assume "Bet B A A''"
            have "A C TS A'' B" 
              by (metis Col_cases \<open>Bet B A A''\<close> assms(1) bet__ts calculation l9_2)
            moreover have "A C OS B C''" 
              by (metis \<open>Bet C'' B C\<close> \<open>C \<noteq> B\<close> assms(1) bet_out_1 invert_one_side 
                  not_col_permutation_2 out_one_side)
            ultimately
            have False 
              by (meson \<open>A C ParStrict A'' C''\<close> l12_6 l9_9 one_side_symmetry 
                  one_side_transitivity)
          }
          moreover 
          {
            assume "Bet A A'' B"
            have "A'' C'' TS A B" 
              using \<open>A C ParStrict A'' C''\<close> \<open>B \<noteq> A''\<close> \<open>Bet A A'' B\<close> 
                bet__ts par_strict_not_col_3 by force
            moreover have "A'' C'' OS B C" 
              by (meson Col_cases TS_def \<open>B \<noteq> C''\<close> \<open>Bet C'' B C\<close> bet_out 
                  calculation invert_one_side out_one_side)
            ultimately have False 
              using \<open>A C ParStrict A'' C''\<close> l9_9 one_side_symmetry 
                one_side_transitivity pars__os3412 by blast
          }
          ultimately have False 
            using \<open>Bet B A A'' \<or> Bet A A'' B\<close> by fastforce
        }
        ultimately have False 
          by blast
      }
      ultimately have ?thesis 
        using Col_def \<open>Col A'' B A\<close> by blast
    }
    moreover {
      assume "Bet B C C''"
      {
        assume "Bet A'' B A"
        have "A C ParStrict A'' C''" 
          by (metis Par_def \<open>A C Par A'' C''\<close> \<open>B \<noteq> C''\<close> \<open>Bet A'' B A\<close> 
              \<open>Col A'' B A\<close> \<open>Col B B C \<and> Col C'' B C\<close> assms(1) bet_neq21__neq 
              l6_21 not_col_permutation_2)
        have "C = C'' \<longrightarrow> ?thesis" 
          using Par_strict_cases \<open>A C ParStrict A'' C''\<close> not_par_strict_id by blast
        moreover 
        { 
          assume "C \<noteq> C''"
          have "A C TS C'' B" 
            by (meson \<open>A C ParStrict A'' C''\<close> \<open>Bet B C C''\<close> \<open>C \<noteq> B\<close> bet__ts 
                between_symmetry invert_two_sides par_strict_comm par_strict_not_col_1)
          have "A C OS B A''" 
            by (metis \<open>A \<noteq> B\<close> \<open>Bet A'' B A\<close> assms(1) bet_out_1 col_permutation_5 out_one_side)
          have "A C TS A'' C''" 
            using \<open>A C OS B A''\<close> \<open>A C ParStrict A'' C''\<close> \<open>A C TS C'' B\<close> l12_6 
              l9_9 one_side_symmetry one_side_transitivity by blast
          hence False 
            by (simp add: \<open>A C ParStrict A'' C''\<close> l12_6 l9_9_bis)
        }
        ultimately have ?thesis 
          by blast  
      }
      moreover have "Bet B A A'' \<longrightarrow> ?thesis" 
        using out2__conga \<open>Bet C'' B C \<Longrightarrow> A B C CongA A'' B C''\<close> \<open>Col A'' B A\<close> 
          \<open>Col C'' B C\<close> calculation l6_4_2 by blast
      moreover have "Bet A A'' B \<longrightarrow> ?thesis" 
        using out2__conga Out_def \<open>B \<noteq> A''\<close> \<open>Bet B C C''\<close> \<open>C \<noteq> B\<close> bet_out_1 by metis
      ultimately have ?thesis 
        using Col_def \<open>Col A'' B A\<close> by blast
    }
    moreover {
      assume "Bet C C'' B"
      {
        assume "Bet A'' B A"
        have "A C ParStrict A'' C''" 
          by (metis Par_def \<open>A C Par A'' C''\<close> \<open>B \<noteq> C''\<close> \<open>Bet A'' B A\<close> \<open>Col A'' B A\<close> 
              \<open>Col B B C \<and> Col C'' B C\<close> assms(1) bet_neq21__neq col_permutation_2 l6_21)
        have "C = C'' \<longrightarrow> ?thesis" 
          using between_trivial calculation(2) by force
        moreover {
          assume "C \<noteq> C''"
          have "A'' C'' TS C B" 
            by (metis Col_cases \<open>A C ParStrict A'' C''\<close> \<open>B \<noteq> C''\<close> \<open>Bet C C'' B\<close> 
                bet__ts invert_two_sides par_strict_not_col_2)
          moreover have "A'' C'' OS B A" 
            using \<open>A C ParStrict A'' C''\<close> \<open>B \<noteq> A''\<close> \<open>Bet A'' B A\<close> 
              bet_out out_one_side par_strict_not_col_3 by presburger
          ultimately have False 
            using \<open>A C ParStrict A'' C''\<close> l9_2 l9_8_2 l9_9 pars__os3412 by blast
        }
        ultimately have ?thesis 
          by blast
      }
      moreover have "Bet B A A'' \<longrightarrow> ?thesis" 
        using \<open>Bet C'' B C \<Longrightarrow> A B C CongA A'' B C''\<close> \<open>Col A'' B A\<close> \<open>Col C'' B C\<close>
          calculation or_bet_out out2__conga by blast
      moreover have "Bet A A'' B \<longrightarrow> ?thesis" 
        using \<open>B \<noteq> A''\<close> \<open>B \<noteq> C''\<close> \<open>Bet C C'' B\<close> bet_out_1 out2__conga by presburger
      ultimately have ?thesis 
        using Col_def \<open>Col A'' B A\<close> by blast
    }
    ultimately show ?thesis
      using Col_def \<open>Col C'' B C\<close> by blast
  qed
  thus ?thesis 
    using \<open>A' B' C' CongA A'' B C''\<close> conga_sym_equiv not_conga by blast
qed

lemma par3_conga3 :
  assumes "\<not> Col A B C" and
    "A B Par A' B'" and
    "B C Par B' C'" and
    "A C Par A' C'" 
  shows "A B C CongA3 A' B' C'" 
proof -
  have "A B C CongA A' B' C'" 
    by (simp add: assms(1) assms(2) assms(3) assms(4) triangle_par)
  moreover have "B C A CongA B' C' A'" 
    by (simp add: assms(1) assms(2) assms(3) assms(4) not_col_permutation_1 
        par_comm triangle_par)
  moreover have "C A B CongA C' A' B'" 
    by (metis Col_cases Par_cases assms(1) assms(2) assms(3) assms(4) triangle_par)
  ultimately show ?thesis 
    by (simp add: CongA3_def)
qed

lemma cong_conga3_cong3:
  assumes "\<not> Col A B C" and
    "Cong A B A' B'" and
    "A B C CongA3 A' B' C'"
  shows "A B C Cong3 A' B' C'" 
  using CongA3_def assms(1) assms(2) assms(3) l11_50_2  Cong3_def by blast

lemma project_par_eqv:
  assumes "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "P Q Par A B" 
  shows "P Q EqV P' Q'" 
proof -
  {
    assume "P Q ParStrict A B"
    {
      assume "Q Q' Par X Y"
      hence "P P' Par Q Q'" 
        by (metis Proj_def \<open>P Q ParStrict A B\<close> assms(1) not_par_one_not_par 
            par_strict_not_col_3)
      have "P' Q' Par A B" 
        by (metis Col_cases Par_def Proj_def \<open>P Q ParStrict A B\<close> assms(1) assms(2) 
            ker_par not_col_distincts par_not_par par_strict_not_col_1 par_symmetry)
      have "P P' ParStrict Q P' \<longrightarrow> Parallelogram P Q Q' P'" 
        using Par_strict_cases not_par_strict_id by blast
      hence "Parallelogram P Q Q' P'" 
        by (metis Col_cases Par_cases Par_def \<open>P P' Par Q Q'\<close> \<open>P' Q' Par A B\<close> assms(1)
            assms(2) assms(3) par_2_plg par_strict_distinct 
            postulate_of_transitivity_of_parallelism_def 
            postulate_of_transitivity_of_parallelism_thm project_col_eq)
    }
    hence "Parallelogram P Q Q' P'" 
      by (metis Col_cases Proj_def \<open>P Q ParStrict A B\<close> assms(2) par_strict_not_col_2)
  }
  hence "Parallelogram P Q Q' P'" 
    by (metis Col_cases Par_def assms(1) assms(2) assms(3) plg_trivial project_id)
  thus ?thesis
    using EqV_def by blast
qed

lemma eqv_project_eq_eq:
  assumes "P Q EqV R S" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "R P' Proj A B X Y" and
    "S S' Proj A B X Y"
  shows "Q' = S'" 
proof (cases "P = Q")
  case True
  thus ?thesis 
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) null_vector project_uniqueness)
next
  case False
  hence "P \<noteq> Q" 
    by simp
  have "R \<noteq> S" 
    using False assms(1) eqv_par par_neq2 by blast
  have "P R EqV Q S" 
    by (simp add: assms(1) eqv_permut)
  have "P = R \<longrightarrow> ?thesis" 
    using assms(1) assms(3) assms(5) project_uniqueness vector_uniqueness by blast
  moreover {
    assume "P \<noteq> R"
    have "Q \<noteq> S" 
      using \<open>P R EqV Q S\<close> \<open>P \<noteq> R\<close> eqv_par par_neq2 by blast
    have "P R Par Q S" 
      using \<open>P R EqV Q S\<close> \<open>P \<noteq> R\<close> eqv_par by blast
    moreover have "P R Par X Y" 
      using \<open>P \<noteq> R\<close> assms(2) assms(4) ker_par by blast
    ultimately have ?thesis 
      using project_par by (meson assms(3) assms(5) par_symmetry par_trans)
  }
  ultimately show ?thesis 
    by blast
qed

lemma eqv_eq_project:
  assumes "P Q EqV R S" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "R P' Proj A B X Y"
  shows "S Q' Proj A B X Y" 
proof (cases "S = Q'") 
  case True
  thus ?thesis
    using Proj_def assms(3) by auto
next
  case False
  hence "S \<noteq> Q'" 
    by simp
  {
    assume "P \<noteq> R"
    hence "P R Par Q S" 
      by (simp add: assms(1) eqv_par eqv_permut)
    have "Col P R P'" 
      using assms(2) assms(4) ker_col by force
    {
      assume "Q Q' Par X Y" 
      have "P R Par X Y" 
        using \<open>P \<noteq> R\<close> assms(2) assms(4) ker_par by auto
      {
        assume "Q Q' Par X Y"
        have "Col S Q Q'" 
          by (metis Par_cases \<open>P R Par Q S\<close> \<open>P R Par X Y\<close> 
              \<open>Q Q' Par X Y\<close> par_id_1 par_not_par)
        have "Q' Q Par X Y" 
          using Par_perm \<open>Q Q' Par X Y\<close> by blast
        hence "S Q' Par X Y" 
          by (metis Col_cases False \<open>Col S Q Q'\<close> col_par par_neq1 par_trans)
      }
      hence "S Q' Par X Y" 
        using \<open>Q Q' Par X Y\<close> by auto
    }
    hence "S Q' Par X Y" 
      by (metis Proj_def \<open>P R Par Q S\<close> \<open>P \<noteq> R\<close> assms(2) assms(3) assms(4) 
          ker_par par_left_comm par_not_par par_symmetry)
    hence ?thesis 
      using Proj_def assms(3) by force
  }
  thus ?thesis
    using assms(1) assms(3) vector_uniqueness by blast
qed

lemma project_par_dir: 
  assumes "P \<noteq> P'" and
    "P P' Proj A B X Y"
  shows "P P' Par X Y" 
  using Proj_def assms(1) assms(2) by presburger

lemma project_idem: 
  assumes "P P' Proj A B X Y"
  shows "P' P' Proj A B X Y" 
  using Proj_def assms by force

lemma eqv_cong: 
  assumes "A B EqV C D"
  shows "Cong A B C D" 
proof -
  have "Parallelogram A B C D \<longrightarrow> ?thesis" 
    using plg_cong by auto
  thus ?thesis 
    using EqV_def assms cong_trivial_identity not_cong_1243 plg_cong_1 by blast
qed

lemma project_preserves_eqv:
  assumes "P Q EqV R S" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "R R' Proj A B X Y" and
    "S S' Proj A B X Y"
  shows "P' Q' EqV R' S'" 
proof (cases "P = Q")
  case True
  thus ?thesis 
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) 
        eqv_trivial null_vector project_uniqueness)
next
  case False
  hence "P \<noteq> Q" 
    by simp
  have "R \<noteq> S" 
    using False assms(1) eqv_par par_neq2 by blast
  {
    assume "P Q Par A B"
    have "P Q EqV P' Q'"
      using project_par_eqv [where ?A="A" and ?B="B" and ?X="X" and ?Y="Y"]
        assms(2) assms(3) \<open>P Q Par A B\<close> by blast
    have "R S EqV R' S'" 
      by (meson False \<open>P Q Par A B\<close> assms(1) assms(4) assms(5) eqv_par 
          par_not_par par_symmetry project_par_eqv)
    hence ?thesis 
      by (meson \<open>P Q EqV P' Q'\<close> assms(1) eqv_sym eqv_trans)
  }
  moreover 
  {
    assume "\<not> P Q Par A B" 
    hence "P Q Par X Y \<longrightarrow> ?thesis" 
      by (metis EqV_def False assms(1) assms(2) assms(3) assms(4) assms(5) 
          eqv_par par_symmetry par_trans project_par)
    moreover
    {
      assume "\<not> P Q Par X Y"
      hence "P' \<noteq> Q'" 
        using False assms(2) assms(3) ker_par by blast
      have "\<not> R S Par X Y" 
        by (metis False \<open>\<not> P Q Par X Y\<close> assms(1) eqv_par par_trans)
      have "R' \<noteq> S'" 
        using \<open>R \<noteq> S\<close> \<open>\<not> R S Par X Y\<close> assms(4) assms(5) ker_par by force
      obtain Q'' where "P Q EqV P' Q''" 
        using vector_construction by blast
      obtain S'' where "R S EqV R' S''" 
        using vector_construction by blast
      hence "P' Q'' EqV R' S''" 
        by (meson \<open>P Q EqV P' Q''\<close> assms(1) eqv_sym eqv_trans)
      {
        assume "Q' = Q''" 
        have "P' \<noteq> Q'" 
          by (simp add: \<open>P' \<noteq> Q'\<close>)
        have "P' Q' Par A B" 
          by (metis Col_cases Par_def Proj_def \<open>P' \<noteq> Q'\<close> assms(2) assms(3))
        hence "P Q Par A B" 
          using False \<open>P Q EqV P' Q''\<close> \<open>Q' = Q''\<close> 
            eqv_par postulate_of_transitivity_of_parallelism_def 
            postulate_of_transitivity_of_parallelism_thm by blast
        hence False 
          by (simp add: \<open>\<not> P Q Par A B\<close>)
      }
      hence "Q' \<noteq> Q''" 
        by blast
      {
        assume "S' = S''" 
        have "P Q Par R S" 
          by (simp add: False assms(1) eqv_par)
        have "P Q Par P' Q''" 
          by (simp add: False \<open>P Q EqV P' Q''\<close> eqv_par)
        have "R S Par R' S'" 
          by (simp add: \<open>R S EqV R' S''\<close> \<open>R \<noteq> S\<close> \<open>S' = S''\<close> eqv_par)
        have "P' Q'' Par R' S'" 
          using \<open>P Q Par P' Q''\<close> \<open>P' Q'' EqV R' S''\<close> \<open>S' = S''\<close> eqv_par 
            par_neq2 by presburger
        have "R' S' Par A B" 
          by (metis Proj_def \<open>R' \<noteq> S'\<close> assms(4) assms(5) par_col2_par_bis par_reflexivity)
        hence "P Q Par A B" 
          using \<open>P Q Par R S\<close> \<open>R S Par R' S'\<close> par_not_par by blast
        hence False 
          by (simp add: \<open>\<not> P Q Par A B\<close>)
      }
      hence "S' \<noteq> S''" 
        by blast
      have "P P' EqV Q Q''" 
        by (simp add: \<open>P Q EqV P' Q''\<close> eqv_permut)
      have "R R' EqV S S''" 
        by (simp add: \<open>R S EqV R' S''\<close> eqv_permut)
      have "P' R' EqV Q'' S''" 
        by (simp add: \<open>P' Q'' EqV R' S''\<close> eqv_permut)
      have "Q'' Q' Proj A B X Y" 
        using \<open>P Q EqV P' Q''\<close> assms(2) assms(3) eqv_eq_project project_idem by blast
      hence "Q'' Q' Par X Y" 
        using \<open>Q' \<noteq> Q''\<close> project_par_dir by auto
      have "S'' S' Proj A B X Y" 
        using \<open>R S EqV R' S''\<close> assms(4) assms(5) eqv_eq_project project_idem by blast
      hence "S'' S' Par X Y" 
        using \<open>S' \<noteq> S''\<close> project_par_dir by auto
      have "Q'' Q' Par S'' S'" 
        using \<open>Q'' Q' Par X Y\<close> \<open>S'' S' Par X Y\<close> not_par_one_not_par by blast
      have "\<not> Col A B Q''" 
        using \<open>Q' \<noteq> Q''\<close> \<open>Q'' Q' Proj A B X Y\<close> project_not_col by auto
      have "\<not> Col P' Q'' Q'" 
        by (metis Proj_def \<open>P' \<noteq> Q'\<close> \<open>\<not> Col A B Q''\<close> assms(2) 
            assms(3) col_permutation_2 colx)
      have "Cong P' Q'' R' S''" 
        using \<open>P' Q'' EqV R' S''\<close> eqv_cong by blast
      moreover have "P' Q'' Q' CongA3 R' S'' S'"
        by (metis Par_def Proj_def \<open>P' Q'' EqV R' S''\<close> \<open>Q'' Q' Par S'' S'\<close>
            \<open>R' \<noteq> S'\<close> \<open>\<not> Col P' Q'' Q'\<close> assms(2) assms(3) assms(4) assms(5) 
            col3 eqv_par not_col_distincts par3_conga3)
      ultimately have "P' Q'' Q' Cong3 R' S'' S'" 
        using cong_conga3_cong3 \<open>\<not> Col P' Q'' Q'\<close> by blast
      {
        assume "Q' = S'" 
        hence "P' = R'" 
          using assms(1) assms(2) assms(3) assms(4) assms(5) eqv_comm 
            eqv_project_eq_eq by blast
        hence "Q'' = S''" 
          using \<open>P' R' EqV Q'' S''\<close> null_vector by blast
        hence "Parallelogram Q'' Q' S' S''" 
          using \<open>Q' = S'\<close> \<open>Q' \<noteq> Q''\<close> plg_trivial by presburger
      }
      moreover 
      {
        assume "Q' \<noteq> S'" 
        have "P' = R' \<longrightarrow> Parallelogram Q'' Q' S' S''" 
          using assms(1) assms(2) assms(3) assms(4) assms(5) calculation 
            eqv_project_eq_eq by blast
        moreover 
        {
          assume "P' \<noteq> R'" 
          have "Q'' \<noteq> S' \<or> Q' \<noteq> S''" 
            using Proj_def \<open>\<not> Col A B Q''\<close> assms(5) by force
          moreover have "\<exists> M .M Midpoint Q'' S' \<and> M Midpoint Q' S''" 
          proof (rule par_cong_mid_os)
            show "Q'' Q' ParStrict S'' S'" 
              by (metis \<open>Q'' Q' Par S'' S'\<close> Par_def \<open>Q' \<noteq> S'\<close> \<open>Q'' Q' Proj A B X Y\<close> 
                  \<open>S'' S' Proj A B X Y\<close> col2__eq project_col_eq)
            show "Cong Q'' Q' S'' S'" 
              using Cong3_def \<open>P' Q'' Q' Cong3 R' S'' S'\<close> by auto
            {
              assume "Parallelogram P' Q'' S'' R'"
              hence "ParallelogramStrict R' P' Q'' S''" 
                by (metis Plg_perm Proj_def \<open>P' \<noteq> R'\<close> \<open>\<not> Col A B Q''\<close> assms(2) 
                    assms(4) colx ncol123_plg__plgs)
              have "Q'' S'' ParStrict Q' S'" 
              proof (rule par_strict_col2_par_strict [where ?C ="R'" and ?D="P'"])
                show "Q' \<noteq> S'" 
                  by (simp add: \<open>Q' \<noteq> S'\<close>)
                show  "Q'' S'' ParStrict R' P'" 
                  using \<open>ParallelogramStrict R' P' Q'' S''\<close> par_strict_symmetry plgs_pars_1 by blast
                show "Col R' P' Q'"       
                  by (metis Proj_def assms(2) assms(3) assms(4) col3)
                show "Col R' P' S'"
                  by (metis Proj_def assms(2) assms(4) assms(5) col3)
              qed
              hence "Q'' S'' OS Q' S'" 
                using l12_6 by blast
            }
            thus "Q'' S'' OS Q' S'"
              using EqV_def \<open>P' Q'' EqV R' S''\<close> \<open>\<not> Col P' Q'' Q'\<close> not_col_distincts by blast
          qed
          ultimately have "Plg Q'' Q' S' S''" 
            by (simp add: Plg_def)
          hence "Parallelogram Q'' Q' S' S''" 
            by (simp add: plg_to_parallelogram)
        }
        ultimately have "Parallelogram Q'' Q' S' S''" 
          by blast
      }
      ultimately have "Parallelogram Q'' Q' S' S''" 
        by blast
      hence "Q'' Q' EqV S'' S'" 
        by (simp add: EqV_def)
      hence ?thesis 
        using \<open>P' Q'' EqV R' S''\<close> eqv_sum by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma perp_projp:
  assumes "P' PerpAt A B P P'"
  shows "P P' Projp A B" 
proof -
  have "A \<noteq> B" 
    using assms perp_in_distinct by auto
  moreover have "Col A B P'" 
    using assms perp_in_col by blast
  moreover have "A B Perp P P'"     
    using assms perp_in_perp by auto
  ultimately show ?thesis
    using Projp_def by blast
qed

lemma proj_distinct:
  assumes "P P' Projp A B"
  shows "P' \<noteq> A \<or> P' \<noteq> B" 
proof -
  have "Col A B P' \<and> A B Perp P P' \<longrightarrow> ?thesis" 
    using perp_distinct by blast
  moreover have "Col A B P \<and> P = P' \<longrightarrow> ?thesis" 
    using Projp_def assms by presburger
  ultimately show ?thesis 
    using Projp_def assms by auto
qed

lemma projp_is_project:
  assumes "P P' Projp A B"
  shows "\<exists> X Y. P P' Proj A B X Y" 
proof -
  have "A \<noteq> B" 
    using Projp_def assms by blast
  moreover
  then obtain X Y where "A B Perp X Y" 
    using perp_vector by blast
  have "X \<noteq> Y" 
    using \<open>A B Perp X Y\<close> perp_not_eq_2 by auto
  moreover have "\<not> A B Par X Y" 
    by (simp add: \<open>A B Perp X Y\<close> perp_not_par)
  moreover have "Col A B P'" 
    using Projp_def assms by fastforce
  moreover have "(P P' Par X Y) \<or> P = P'" 
    by (metis Projp_def \<open>A B Perp X Y\<close> assms par_perp2__par par_reflexivity)
  ultimately show ?thesis 
    using Proj_def by blast
qed

lemma projp_is_project_perp:
  assumes "P P' Projp A B" 
  shows "\<exists> X Y. P P' Proj A B X Y \<and> A B Perp X Y" 
proof -
  have "A \<noteq> B" 
    using Projp_def assms by blast
  moreover
  then obtain X Y where "A B Perp X Y" 
    using perp_vector by blast
  moreover
  have "X \<noteq> Y" 
    using \<open>A B Perp X Y\<close> perp_not_eq_2 by auto
  moreover have "\<not> A B Par X Y" 
    by (simp add: \<open>A B Perp X Y\<close> perp_not_par)
  moreover have "Col A B P'" 
    using Projp_def assms by fastforce
  moreover have "(P P' Par X Y) \<or> P = P'" 
    by (metis Projp_def \<open>A B Perp X Y\<close> assms par_perp2__par par_reflexivity)
  ultimately show ?thesis 
    using Proj_def by blast
qed

lemma projp_to_project:
  assumes "A B Perp X Y" and
    "P P' Projp A B"
  shows "P P' Proj A B X Y" 
proof -
  have "A \<noteq> B" 
    using assms(1) perp_distinct by auto
  moreover have "X \<noteq> Y" 
    using assms(1) perp_distinct by blast
  moreover have "\<not> A B Par X Y" 
    by (simp add: \<open>A B Perp X Y\<close> perp_not_par)
  moreover have "Col A B P'" 
    using Projp_def assms(2) by fastforce
  moreover have "(P P' Par X Y) \<or> P = P'" 
    by (metis Projp_def \<open>A B Perp X Y\<close> assms(2) par_perp2__par par_reflexivity)
  ultimately show ?thesis 
    using Proj_def by blast
qed

lemma project_to_projp:
  assumes "P P' Proj A B X Y" and
    "A B Perp X Y" 
  shows "P P' Projp A B" 
proof -
  have "A \<noteq> B" 
    using assms(2) perp_not_eq_1 by auto
  moreover have "Col A B P'" 
    using Proj_def assms(1) by force
  moreover
  {
    assume "P P' Par X Y"
    have "Col A B P'" 
      using calculation(2) by blast
    moreover have "A B Perp P P'" 
      using Perp_cases \<open>P P' Par X Y\<close> assms(2) par_perp__perp par_symmetry by blast
    ultimately have "Col A B P' \<and> A B Perp P P'" 
      by blast
  }
  ultimately show ?thesis 
    using Proj_def Projp_def assms(1) by auto
qed

lemma projp_project_to_perp:
  assumes "P \<noteq> P'" and
    "P P' Projp A B" and 
    "P P' Proj A B X Y"
  shows "A B Perp X Y" 
  by (metis Perp_perm Projp_def assms(1) assms(2) assms(3) par_perp__perp project_par_dir)

lemma project_par_project:
  assumes "P P' Proj A B X Y" and
    "X Y Par X' Y'"
  shows "P P' Proj A B X' Y'" 
  by (metis Proj_def assms(1) assms(2) not_par_one_not_par par_neq2 par_symmetry)


lemma project_project_par :
  assumes "P \<noteq> P'" and
    "P P' Proj A B X Y" and
    "P P' Proj A B X' Y'"
  shows "X Y Par X' Y'" 
proof -
  have "P P' Par X Y \<longrightarrow> ?thesis" 
    using assms(1) assms(3) par_not_par par_symmetry project_par_dir by blast
  thus ?thesis 
    using assms(1) assms(2) project_par_dir by blast
qed

lemma projp_id:
  assumes "P P' Projp A B" and 
    "P Q' Projp A B" 
  shows "P' = Q'" 
proof -
  have "Col A B P' \<and> A B Perp P P' \<longrightarrow> ?thesis" 
    by (metis Projp_def assms(2) l8_18_uniqueness perp_not_col2)
  moreover have "Col A B P \<and> P = P' \<longrightarrow> ?thesis" 
    by (metis Projp_def assms(2) perp_not_col2)
  ultimately show ?thesis 
    using Projp_def assms(1) by force
qed

lemma projp_preserves_bet:
  assumes "Bet A B C" and
    "A A' Projp X Y" and
    "B B' Projp X Y" and
    "C C' Projp X Y"
  shows "Bet A' B' C'" 
proof -
  obtain T U where "A A' Proj X Y T U" and "X Y Perp T U" 
    using assms(2) projp_is_project_perp by blast
  thus ?thesis 
    using assms(1) assms(3) assms(4) project_preserves_bet projp_to_project by blast
qed

lemma projp_preserves_eqv:
  assumes "A B EqV C D" and
    "A A' Projp X Y" and
    "B B' Projp X Y" and
    "C C' Projp X Y" and
    "D D' Projp X Y"
  shows "A' B' EqV C' D'" 
proof -
  obtain T U where "A A' Proj X Y T U" and "X Y Perp T U" 
    using assms(2) projp_is_project_perp by blast
  thus ?thesis 
    using assms(1) assms(3) assms(4) assms(5) project_preserves_eqv projp_to_project by blast
qed

lemma projp_idem:
  assumes "P P' Projp A B" 
  shows "P' P' Projp A B" 
  using Projp_def assms by force

lemma projp2_col:
  assumes "P A Projp B C" and
    "Q A Projp B C"
  shows "Col A P Q" 
proof -
  {
    assume "Col B C A" and "B C Perp P A" 
    {
      assume "Col B C A" and "B C Perp Q A"
      have ?thesis 
      proof (rule perp2__col [where ?A="B" and ?B="C"])
        show "A P Perp B C"   
          using Perp_cases \<open>B C Perp P A\<close> by auto
        show "A Q Perp B C"
          using Perp_perm \<open>B C Perp Q A\<close> by blast
      qed
    }
    moreover
    have "Col B C Q \<and> Q = A \<longrightarrow> ?thesis" 
      by (simp add: col_trivial_3)
    ultimately have ?thesis 
      using Projp_def assms(2) by force
  }
  moreover have "Col B C P \<and> P = A \<longrightarrow> ?thesis" 
    by (simp add: col_trivial_1)
  ultimately show ?thesis 
    using Projp_def assms(1) by force
qed

lemma projp_projp_perp:
  assumes "P1 \<noteq> P2" and
    "P1 P Projp Q1 Q2" and
    "P2 P Projp Q1 Q2" 
  shows "P1 P2 Perp Q1 Q2" 
proof -
  have "Col P1 P P2" 
    by (metis Col_cases Perp_cases Projp_def assms(2) assms(3) not_col_distincts perp2__col)
  thus ?thesis 
    by (metis Perp_cases Projp_def assms(1) assms(2) assms(3) not_col_distincts perp_col2_bis)
qed

lemma col_projp_eq: 
  assumes "Col A B P" and
    "P P' Projp A B"
  shows "P = P'" 
  by (meson Projp_def assms(1) assms(2) perp_not_col2)

lemma projp_col:
  assumes "P P' Projp A B"
  shows "Col A B P'" 
  using Projp_def assms by force

lemma perp_projp2_eq:
  assumes "A A' Projp C D" and 
    "B B' Projp C D" and
    "A B Perp C D"
  shows "A' = B'" 
proof -
  {
    assume "Col C D A'" and "C D Perp A A'"
    {
      assume "Col C D B'" and "C D Perp B B'" 
      {
        assume "\<not> Col A B C" 
        have "Col A B A'" 
          using Perp_cases \<open>C D Perp A A'\<close> assms(3) perp2__col by blast
        moreover have "Col A B B'" 
          using Col_cases Perp_cases \<open>C D Perp B B'\<close> assms(3) perp2__col by meson
        ultimately have "A' = B'" 
          using \<open>Col C D A'\<close> \<open>Col C D B'\<close> assms(3) l8_14_1 perp_col4 by blast
      }
      moreover {
        assume "\<not> Col A B D" 
        have "Col A B A'" 
          using Perp_cases \<open>C D Perp A A'\<close> assms(3) perp2__col by blast
        moreover have "Col A B B'" 
          using Col_cases Perp_cases \<open>C D Perp B B'\<close> assms(3) perp2__col by meson
        ultimately have  "A' = B'" 
          using \<open>Col C D A'\<close> \<open>Col C D B'\<close> assms(3) perp_col0 perp_not_col2 by blast
      }
      ultimately have ?thesis 
        using assms(3) perp_not_col2 by blast
    }
    moreover have "Col C D B \<and> B = B' \<longrightarrow> ?thesis" 
      using Perp_cases \<open>C D Perp A A'\<close> \<open>Col C D A'\<close> assms(3) l8_18_uniqueness by blast
    ultimately have ?thesis 
      using Projp_def assms(2) by force
  }
  moreover have "Col C D A \<and> A = A'\<longrightarrow> ?thesis" 
    by (metis Perp_cases Projp_def assms(2) assms(3) l8_18_uniqueness perp_not_col2)
  ultimately show ?thesis 
    using Projp_def assms(1) by force
qed

lemma col_par_projp2_eq:
  assumes "Col L11 L12 P" and
    "L11 L12 Par L21 L22" and
    "P P' Projp L21 L22" and
    "P' P'' Projp L11 L12" 
  shows "P = P''" 
proof -
  {
    assume "Col L21 L22 P'" and "L21 L22 Perp P P'" and
      "Col L11 L12 P''" and "L11 L12 Perp P' P''"
    have "P P' Par P' P''" 
      using Par_cases \<open>L11 L12 Perp P' P''\<close> \<open>L21 L22 Perp P P'\<close> assms(2) 
        par_perp2__par by blast
    have "\<not> Col L11 L12 P' \<longrightarrow> ?thesis" 
      by (metis Par_perm Perp_perm \<open>Col L11 L12 P''\<close> \<open>L11 L12 Perp P' P''\<close> 
          \<open>L21 L22 Perp P P'\<close> assms(1) assms(2) l8_18_uniqueness par_perp__perp)
    moreover have "\<not> Col L11 L12 P'' \<longrightarrow> ?thesis" 
      using \<open>Col L11 L12 P''\<close> by blast
    ultimately have "P = P''" 
      using perp_not_col2 \<open>L11 L12 Perp P' P''\<close> by blast
  }
  thus ?thesis 
    by (metis Projp_def assms(1) assms(2) assms(3) assms(4) col_not_col_not_par 
        col_projp_eq par_symmetry)
qed

lemma col_2_par_projp2_cong:
  assumes "Col L11 L12 A'" and
    "Col L11 L12 B'" and
    "L11 L12 Par L21 L22" and
    "A' A Projp L21 L22" and
    "B' B Projp L21 L22"
  shows "Cong A B A' B'" 
proof -
  {
    assume "L11 L12 ParStrict L21 L22" 
    {
      assume "A' \<noteq> B'" 
      {
        assume "A \<noteq> B"
        have "L11 L12 ParStrict A B" 
          using \<open>A \<noteq> B\<close> \<open>L11 L12 ParStrict L21 L22\<close> assms(4) assms(5) 
            par_strict_col2_par_strict projp_col by blast
        hence "A B ParStrict B' A'" 
          by (metis Par_strict_cases \<open>A' \<noteq> B'\<close> assms(1) assms(2) par_strict_col2_par_strict)
        moreover have "A A' Par B B'" 
          by (metis Par_perm Projp_def \<open>L11 L12 ParStrict L21 L22\<close> 
              assms(1) assms(2) assms(3) assms(4) assms(5) not_strict_par2 
              par_perp2__par par_perp__perp par_strict_not_col_4)
        ultimately have "Plg A B B' A'" 
          by (simp add: pars_par_plg)
        hence ?thesis 
          using Plg_perm plg_cong_2 plg_to_parallelogram by blast
      }
      moreover {
        assume "A = B"
        hence "Col A A' B'" 
          using assms(4) assms(5) projp2_col by auto
        moreover have "Col L21 L22 A" 
          using assms(4) projp_col by blast
        ultimately have False using l6_21 
          by (metis \<open>A' \<noteq> B'\<close> \<open>L11 L12 ParStrict L21 L22\<close> 
              assms(1) assms(2) col_trivial_2 not_col_permutation_1 par_not_col)
      }
      ultimately have ?thesis 
        by blast
    }
    hence ?thesis 
      using assms(4) assms(5) cong_trivial_identity projp_id by blast
  }
  thus ?thesis 
    by (metis Par_cases assms(1) assms(2) assms(3) assms(4) assms(5) col_projp_eq 
        cong_reflexivity par_not_col_strict par_strict_symmetry)
qed

end

subsubsection "Pappus' theorem in neutral geometry"

context Tarski_neutral_dimensionless

begin

lemma l13_10_aux1:
  assumes "Col PO A B" and
    "Col PO P Q" and
    "PO P Perp P A" and
    "PO Q Perp Q B" and
    "QCong la" and 
    "QCong lb" and
    "QCong lp" and
    "QCong lq" and
    "la PO A" and
    "lb PO B" and
    "lp PO P" and
    "lq PO Q"
  shows "\<exists> a. QCongAAcute a \<and> Lcos lp la a \<and> Lcos lq lb a" 
proof -
  have "Acute A PO P" 
  proof (rule perp_acute [where ?C="P"])
    show "Col A P P" 
      using col_trivial_2 by auto
    show "P PerpAt PO P A P" 
      by (simp add: assms(3) col_trivial_2 l8_15_1 perp_right_comm)
  qed
  have "P \<noteq> PO" 
    using assms(3) perp_distinct by blast
  have "A \<noteq> PO" 
    using \<open>Acute A PO P\<close> acute_distincts by presburger
  have "Q \<noteq> PO" 
    using assms(4) perp_distinct by blast
  have "B \<noteq> PO" 
    using assms(4) col_trivial_2 perp_not_col by blast
  obtain a where "QCongAAcute a" and "a A PO P" 
    using \<open>Acute A PO P\<close> ex_anga by blast
  have "\<not> PO P Par A P" 
    using Par_cases assms(3) perp_not_par by blast
  have "A \<noteq> P" 
    using assms(3) perp_distinct by blast
  have "PO PO Proj PO P A P" 
    using Proj_def \<open>A \<noteq> P\<close> \<open>P \<noteq> PO\<close> \<open>\<not> PO P Par A P\<close> col_trivial_3 by presburger
  have "A P Proj PO P A P" 
    using Proj_def \<open>A \<noteq> P\<close> \<open>P \<noteq> PO\<close> \<open>\<not> PO P Par A P\<close> col_trivial_2 par_reflexivity by auto
  have "B Q Par A P" 
  proof (rule l12_9 [where ?C1.0="PO" and ?C2.0="P"])
    show "Coplanar PO P B A" 
      using assms(1) ncop__ncols not_col_permutation_5 by blast
    show "Coplanar PO P B P" 
      using ncop_distincts by blast
    show "Coplanar PO P Q A" 
      using assms(2) ncop__ncols by blast
    show "Coplanar PO P Q P" 
      using ncop_distincts by blast
    show "B Q Perp PO P" 
      by (metis Col_cases Perp_cases \<open>P \<noteq> PO\<close> assms(2) assms(4) perp_col)
    show "A P Perp PO P" 
      using Perp_perm assms(3) by blast
  qed
  hence "B Q Proj PO P A P" 
    unfolding Proj_def using \<open>A \<noteq> P\<close> \<open>P \<noteq> PO\<close> \<open>\<not> PO P Par A P\<close> assms(2) by blast
  {
    assume "Bet PO A B"
    have "Bet PO P Q"
    proof (rule per23_preserves_bet [where ?B="A" and ?C="B"],simp_all add: \<open>Bet PO A B\<close> assms(2))
      show "PO \<noteq> P" 
        using \<open>P \<noteq> PO\<close> by blast 
      show "PO \<noteq> Q" 
        using \<open>Q \<noteq> PO\<close> by blast
      show "Per PO P A" 
        by (simp add: assms(3) perp_comm perp_per_1)
      show "Per PO Q B" 
        using assms(4) perp_comm perp_per_1 by blast
    qed
    have "A PO P CongA B PO Q"
    proof (rule out2__conga)
      show "PO Out B A" 
        by (simp add: Out_def \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> \<open>Bet PO A B\<close>)
      show "PO Out Q P" 
        using Out_def \<open>Bet PO P Q\<close> \<open>P \<noteq> PO\<close> \<open>Q \<noteq> PO\<close> by blast
    qed
    hence "a B PO Q" 
      using \<open>QCongAACute a\<close> \<open>a A PO P\<close> anga_conga_anga by blast
  }
  moreover 
  {
    assume "Bet A B PO"
    have "Bet PO Q P" 
    proof (rule per23_preserves_bet [where ?B="B" and ?C="A"])
      show "Bet PO B A" 
        using Bet_cases \<open>Bet A B PO\<close> by blast
      show "PO \<noteq> Q" 
        using \<open>Q \<noteq> PO\<close> by auto
      show "PO \<noteq> P" 
        using \<open>P \<noteq> PO\<close> by blast
      show "Col PO Q P" 
        using Col_cases assms(2) by auto
      show "Per PO Q B" 
        by (simp add: assms(4) perp_comm perp_per_1)
      show "Per PO P A" 
        by (simp add: assms(3) perp_left_comm perp_per_2)
    qed
    hence "Bet P Q PO" 
      using Bet_cases by blast
    have "A PO P CongA B PO Q"
    proof (rule out2__conga)
      show "PO Out B A" 
        by (simp add: \<open>B \<noteq> PO\<close> \<open>Bet A B PO\<close> bet_out_1)
      show "PO Out Q P" 
        by (simp add: \<open>Bet P Q PO\<close> \<open>Q \<noteq> PO\<close> bet_out_1)
    qed
    hence "a B PO Q" 
      using \<open>QCongAACute a\<close> \<open>a A PO P\<close> anga_conga_anga by blast
  }
  moreover 
  {
    assume "Bet B PO A"
    have "Bet Q PO P" 
    proof (rule per13_preserves_bet [where ?A="B" and ?C="A"])
      show "Bet B PO A" 
        by (simp add: \<open>Bet B PO A\<close>)
      show "PO \<noteq> Q" 
        using \<open>Q \<noteq> PO\<close> by auto
      show "PO \<noteq> P" 
        using \<open>P \<noteq> PO\<close> by blast
      show "Col Q PO P" 
        using Col_cases assms(2) by blast
      show "Per PO Q B" 
        by (simp add: assms(4) perp_comm perp_per_1)
      show "Per PO P A" 
        using Perp_cases assms(3) perp_per_1 by blast
    qed
    have "A PO P CongA B PO Q" 
      using \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> \<open>Bet B PO A\<close> \<open>Bet Q PO P\<close> \<open>P \<noteq> PO\<close> \<open>Q \<noteq> PO\<close> 
        conga_sym_equiv l11_14 by blast
    hence "a B PO Q" 
      using \<open>QCongAACute a\<close> \<open>a A PO P\<close> anga_conga_anga by blast
  }
  ultimately have "a B PO Q" 
    using Col_def assms(1) by blast
  have "QCongAAcute a" 
    by (simp add: \<open>QCongAACute a\<close>)
  moreover have "Lcos lp la a"
  proof -
    have "Per A P PO" 
      using Perp_perm assms(3) perp_per_2 by blast
    moreover have "a P PO A" 
      using \<open>a A PO P\<close> anga_sym \<open>QCongAACute a\<close> by blast
    ultimately show ?thesis
      using assms(11) assms(9) Lcos_def \<open>QCongAACute a\<close> assms(5) assms(7) by auto
  qed
  moreover have "Lcos lq lb a" 
  proof -
    have "Per B Q PO" 
      using Perp_perm assms(4) perp_per_1 by blast
    moreover have "a Q PO B" 
      by (simp add: \<open>QCongAACute a\<close> \<open>a B PO Q\<close> anga_sym)
    ultimately show ?thesis
      using assms(10) assms(12) Lcos_def \<open>QCongAACute a\<close> assms(6) assms(8) by auto
  qed
  ultimately show ?thesis
    by blast
qed

lemma l13_10_aux2:
  assumes "Col PO A B" and
    "QCong la" and
    "QCong lla" and
    "QCong lb" and
    "QCong llb" and
    "la PO A" and
    "lla PO A" and
    "lb PO B" and
    "llb PO B" and
    "A \<noteq> PO" and
    "B \<noteq> PO" 
  shows "\<exists> a. QCongAAcute a \<and> Lcos lla la a \<and> Lcos llb lb a" 
proof -
  have "Acute A PO A" 
    using acute_trivial assms(10) by auto
  then obtain a where "QCongAAcute a" and "a A PO A" 
    using anga_exists ex_anga by fastforce
  have "Col A PO A" 
    using not_col_distincts by blast
  hence "QCongANullAcute a" 
    using anga_col_null \<open>QCongAACute a\<close> \<open>a A PO A\<close> by blast
  have "la EqLTarski lla" 
    using assms(2) assms(3) assms(6) assms(7) ex_eqL by auto
  moreover 
  have "Lcos la la a"
  proof (rule null_lcos)
    show "QCong la"     
      by (simp add: assms(2))
    show "\<not> QCongNull la"     
      using assms(10) assms(2) assms(6) between_cong lg_cong 
        lg_null_instance not_bet_distincts by blast
    show "QCongANullAcute a"
      by (simp add: \<open>QCongANullAcute a\<close>)
  qed
  ultimately have "Lcos lla la a" 
    using l13_6 lcos_eql_lcos by blast
  moreover have "Lcos llb lb a" 
  proof -
    obtain b where "QCongAAcute b" and "b B PO B" 
      using anga_exists acute_trivial assms(11) by blast
    have "a EqA b" using null_anga 
      using AngAcute_def \<open>QCongAACute a\<close> \<open>QCongAACute b\<close> \<open>a A PO A\<close> \<open>b B PO B\<close> by presburger
    have "lb EqLTarski llb" 
      using assms(4) assms(5) assms(8) assms(9) ex_eqL by blast
    have "\<not> QCongNull lb" 
      using assms(11) assms(4) assms(8) cong_identity lg_cong lg_null_instance by blast
    hence "Lcos lb lb a" 
      using null_lcos assms(4) \<open>QCongANullAcute a\<close> by blast
    thus ?thesis 
      using \<open>lb EqLTarski llb\<close> l13_6 lcos_eql_lcos by blast
  qed
  ultimately show ?thesis 
    using \<open>QCongAACute a\<close> by blast
qed

lemma l13_6_bis:
  assumes "Lcos lp l1 a" and
    "Lcos lp l2 a"
  shows "l1 EqLTarski l2" 
proof -
  have "QCongANullAcute a \<longrightarrow> ?thesis" 
    by (metis (full_types) EqLTarski_def assms(1) assms(2) null_lcos_eql)
  moreover 
  {
    assume "\<not> QCongANullAcute a"
    obtain A B C where "Per C B A" and "lp A B" and "l2 A C" and "a B A C" 
      using Lcos_def assms(2) by auto
    obtain A' B' C' where "Per C' B' A'" and "lp A' B'" and "l1 A' C'" and "a B' A' C'" 
      using Lcos_def assms(1) by auto
    {
      assume "B = C"
      hence "Col B A B" 
        by (simp add: col_trivial_3)
      hence "Col B A C" 
        by (simp add: \<open>B = C\<close> col_trivial_2)
      moreover 
      have "QCongAACute a" 
        using lcos_lg_anga assms(2) by blast
      hence "\<not> Col B A C"
        using not_null_not_col [where ?a="a"] \<open>\<not> QCongANullAcute a\<close> \<open>a B A C\<close> by blast
      ultimately have False 
        by blast
    }
    hence "B \<noteq> C" 
      by blast
    {
      assume "B' = C'"
      hence "Col B' A' B'" 
        by (simp add: col_trivial_3)
      hence "Col B' A' C'" 
        by (simp add: \<open>B' = C'\<close> col_trivial_2)
      moreover 
      have "QCongAACute a" 
        using lcos_lg_anga assms(2) by blast
      hence "\<not> Col B' A' C'"
        using not_null_not_col [where ?a="a"] \<open>\<not> QCongANullAcute a\<close> \<open>a B' A' C'\<close> by blast
      ultimately have False 
        by blast
    }
    hence "B' \<noteq> C'" 
      by blast
    have "A \<noteq> B" 
      using \<open>lp A B\<close> assms(2) lcos_const_cb lcos_lg_distincts by blast
    have "A \<noteq> C" 
      using \<open>A \<noteq> B\<close> \<open>Per C B A\<close> per_distinct by blast
    have "QCong lp" 
      using assms(1) Lcos_def by blast
    hence "Cong A B A' B'" 
      using lg_cong [where ?l = "lp"] \<open>lp A B\<close> \<open>lp A' B'\<close> by blast
    have "QCongAACute a" 
      using lcos_lg_anga assms(2) by blast
    hence "B A C CongA B' A' C'" 
      using anga_conga [where ?a = "a"] \<open>a B A C\<close> \<open>a B' A' C'\<close> by blast
    have "C B A CongA C' B' A'" 
      using l11_16 \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>B' = C' \<Longrightarrow> False\<close> \<open>Cong A B A' B'\<close> \<open>Per C B A\<close> 
        \<open>Per C' B' A'\<close> cong_diff by blast
    hence "A B C CongA A' B' C'" 
      by (simp add: conga_comm)
    hence "Cong A C A' C' \<and> Cong B C B' C' \<and> A C B CongA A' C' B'" 
      using l11_50_1 \<open>B A C CongA B' A' C'\<close>  \<open>Cong A B A' B'\<close> Col_cases 
        \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>Per C B A\<close> per_col_eq by blast
    have "Cong A C A' C'" 
      using \<open>Cong A C A' C' \<and> Cong B C B' C' \<and> A C B CongA A' C' B'\<close> by auto
    have "QCong l1" 
      using assms(1) Lcos_def by blast
    have "QCong l2" 
      using assms(2) Lcos_def by blast
    have "TarskiLen A' C' l1" 
      using \<open>l1 A' C'\<close> TarskiLen_def \<open>QCong l1\<close> by blast
    moreover have "l2 A' C'"
      using lg_cong_lg [where ?A = "A" and ?B = "C"] \<open>QCong l2\<close> \<open>l2 A C\<close> 
        \<open>Cong A C A' C'\<close> by blast
    hence "TarskiLen A' C' l2" 
      using TarskiLen_def \<open>QCong l2\<close> by blast
    ultimately have ?thesis 
      using all_eql by force
  }
  ultimately show ?thesis by blast
qed

lemma lcos3_lcos2:
  assumes "EqLcos3 l1 a b n l2 c d n"
  shows "EqLcos2 l1 a b l2 c d"
proof -
  obtain lp where "Lcos3 lp l1 a b n" and "Lcos3 lp l2 c d n" 
    using EqLcos3_def assms by blast
  obtain ll1 where "Lcos2 ll1 l1 a b" and "Lcos lp ll1 n" 
    using \<open>Lcos3 lp l1 a b n\<close> lcos3_lcos_2_1 by fastforce
  obtain ll2 where "Lcos2 ll2 l2 c d" and "Lcos lp ll2 n" 
    using \<open>Lcos3 lp l2 c d n\<close> lcos3_lcos_2_1 by blast
  have "ll1 EqLTarski ll2" 
    using l13_6_bis [where ?lp = "lp" and ?a = "n"] \<open>Lcos lp ll1 n\<close> \<open>Lcos lp ll2 n\<close> by blast
  have "Lcos2 ll1 l2 c d" 
  proof (rule lcos2_eql_lcos2 [where ?lla="l2" and ?la="ll2"])
    show "Lcos2 ll2 l2 c d" 
      by (simp add: \<open>Lcos2 ll2 l2 c d\<close>)
    show "l2 EqLTarski l2" 
      by (simp add: EqLTarski_def)
    show "ll2 EqLTarski ll1" 
      using EqLTarski_def \<open>ll1 EqLTarski ll2\<close> by auto
  qed
  thus ?thesis 
    using \<open>Lcos2 ll1 l1 a b\<close> EqLcos2_def by blast
qed

lemma lcos2_lcos:
  assumes "EqLcos2 l1 a c l2 b c"
  shows "EqLcos l1 a l2 b" 
proof -
  obtain lp where "Lcos2 lp l1 a c" and "Lcos2 lp l2 b c" 
    using EqLcos2_def assms by blast
  then obtain lx where "Lcos lx l1 a" and "Lcos lp lx c" 
    using Lcos2_def by blast
  obtain ly where "Lcos ly l2 b" and "Lcos lp ly c" 
    using Lcos2_def \<open>Lcos2 lp l2 b c\<close> by auto
  hence "Lcos lx l2 b" 
    by (meson \<open>Lcos lp lx c\<close> l13_6_bis lcos_eql_lcos)
  thus ?thesis 
    using \<open>Lcos lx l1 a\<close> EqLcos_def by blast
qed

lemma lcos_per_anga: 
  assumes "Lcos lp la a" and
    "la PO A" and
    "lp PO P" and
    "Per A P PO"
  shows "a A PO P" 
proof -
  obtain A' P' O' where "Per A' P' O'" and "lp O' P'" and "la O' A'" and "a P' O' A'" 
    using assms(1) Lcos_def by blast
  have "QCong la" 
    using assms(1) Lcos_def by blast
  hence "Cong PO A O' A'"
    using lg_cong [where ?l = "la"] assms(2) \<open>la O' A'\<close> by blast
  have "QCong lp" 
    using assms(1) Lcos_def by blast
  hence "Cong PO P O' P'" 
    using lg_cong [where ?l = "lp"] assms(3) \<open>lp O' P'\<close> by blast
  have "\<not> QCongNull lp" 
    using lcos_lg_not_null assms(1) by blast
  have "\<not> QCongNull la" 
    using lcos_lg_not_null assms(1) by blast
  {
    assume "A = P" 
    have "Cong O' A' O' P'" 
      using \<open>A = P\<close> \<open>Cong PO A O' A'\<close> \<open>Cong PO P O' P'\<close> cong_inner_transitivity by blast
    have "A' = P'" 
    proof -
      {
        assume "Col A' P' O'"
        have "A' = P' \<or> O' = P'" 
          using \<open>Col A' P' O'\<close> \<open>Per A' P' O'\<close> l8_9 by auto
        moreover have "O' = P' \<longrightarrow> A' = P'" 
          using \<open>Cong O' A' O' P'\<close> cong_identity by blast
        ultimately have ?thesis 
          by blast
      }
      moreover 
      {
        assume "\<not> Col A' P' O'"
        have False
          by (metis \<open>Cong O' A' O' P'\<close> \<open>Per A' P' O'\<close> \<open>\<not> Col A' P' O'\<close> 
              cong__nlt not_col_distincts not_cong_4312 per_lt)
      }
      ultimately show ?thesis 
        by blast
    qed
    have "QCongANullAcute a"
    proof (rule out_null_anga [where ?A="P'" and ?B="O'" and ?C="P'"])
      show "QCongAACute a" 
        using assms(1) Lcos_def by blast
      show "a P' O' P'" 
        using \<open>A' = P'\<close> \<open>a P' O' A'\<close> by auto
      have "P' \<noteq> O'" 
        using \<open>A' = P'\<close> \<open>a P' O' P'\<close> \<open>la O' A'\<close> assms(1) lcos_lg_distincts by blast
      thus "O' Out P' P'" 
        by (simp add: out_trivial)
    qed
    moreover have "P \<noteq> PO" 
      using \<open>Cong PO P O' P'\<close> \<open>lp O' P'\<close> assms(1) cong_diff_4 lcos_const_cb 
        lcos_lg_distincts by blast
    ultimately have ?thesis 
      by (simp add: \<open>A = P\<close> is_null_all)
  }
  moreover 
  {
    assume "A \<noteq> P"
    have "PO \<noteq> P" 
      using assms(1) assms(3) lcos_const_cb lcos_lg_distincts by blast
    hence "Col A P PO \<longrightarrow> ?thesis"
      using \<open>A \<noteq> P\<close> assms(4) l8_9 by blast
    moreover
    {
      assume "\<not> Col A P PO" 
      have "P' \<noteq> O' \<or> A' \<noteq> O'" 
        using \<open>A \<noteq> P\<close> \<open>Cong PO A O' A'\<close> \<open>Cong PO P O' P'\<close> cong_identity by blast
      {
        assume "A' = P'"
        have "Cong PO P PO A" 
          using Cong_perm \<open>A' = P'\<close> \<open>Cong PO A O' A'\<close> \<open>Cong PO P O' P'\<close> 
            cong_transitivity by blast
        moreover have "P A Lt A PO \<and> P PO Lt A PO" 
          using \<open>A \<noteq> P\<close> \<open>PO \<noteq> P\<close> assms(4) lt_left_comm per_lt by blast
        ultimately have False 
          using cong__nlt not_cong_2143 by blast
      }
      hence "A' \<noteq> P'" 
        by blast
      have "A P PO CongA A' P' O'" 
        using \<open>A \<noteq> P\<close> \<open>A' \<noteq> P'\<close> \<open>Cong PO P O' P'\<close> \<open>PO \<noteq> P\<close> \<open>Per A' P' O'\<close> assms(4) 
          cong_diff l11_16 by blast
      have "Cong P A P' A' \<and> P A PO CongA P' A' O' \<and> P PO A CongA P' O' A'" 
        by (metis \<open>A \<noteq> P\<close> \<open>Cong PO A O' A'\<close> \<open>Cong PO P O' P'\<close> \<open>PO \<noteq> P\<close> 
            \<open>Per A' P' O'\<close> assms(4) cong2_per2__cong l11_51 not_cong_2143 per_distinct)
      have "QCongAACute a" 
        using assms(1) Lcos_def by blast
      moreover have "a A' O' P'" 
        by (simp add: \<open>a P' O' A'\<close> anga_sym calculation)
      moreover have "A' O' P' CongA A PO P" 
        by (simp add: \<open>Cong P A P' A' \<and> P A PO CongA P' A' O' \<and> P PO A CongA P' O' A'\<close> 
            conga_comm conga_sym_equiv)
      ultimately have ?thesis 
        using anga_conga_anga by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma lcos_lcos_cop__col:
  assumes "Lcos lp la a" and
    "Lcos lp lb b" and
    "la PO A" and
    "lb PO B" and
    "lp PO P" and
    "a A PO P" and
    "b B PO P" and
    "Coplanar PO A B P"
  shows "Col A B P" 
proof -
  have "QCong la" 
    using assms(1) Lcos_def by blast
  have "QCong lp" 
    using assms(1) Lcos_def by blast
  have "QCong lb" 
    using assms(2) Lcos_def by blast
  have "QCongAACute a" 
    using assms(1) Lcos_def by blast
  have "QCongAACute b" 
    using assms(2) Lcos_def by blast
  have "Per PO P A" 
    using lcos_per \<open>QCong la\<close> \<open>QCong lp\<close> \<open>QCongAACute a\<close> anga_sym assms(1) 
      assms(3) assms(5) assms(6) by blast
  have "Per PO P B" 
    using lcos_per \<open>QCong lb\<close> \<open>QCong lp\<close> \<open>QCongAACute b\<close> anga_sym assms(2) 
      assms(4) assms(5) assms(7) by blast
  show ?thesis
  proof (rule cop_per2__col [where ?A="PO"], simp add: assms(8))
    show "PO \<noteq> P" 
      using assms(1) assms(5) lcos_const_cb lcos_lg_distincts by blast
    show "Per A P PO" 
      using \<open>Per PO P A\<close> l8_2 by blast
    show "Per B P PO" 
      using Per_cases \<open>Per PO P B\<close> by auto
  qed
qed

lemma per13_preserves_bet_inv: 
  assumes "Bet A' B C'" and
    "B \<noteq> A'" and 
    "B \<noteq> C'" and
    "Col A B C" and 
    "Per B A' A" and
    "Per B C' C" 
  shows "Bet A B C" 
proof -
  have "Col A' B C'" 
    by (simp add: assms(1) bet_col)
  {
    assume "A = A'"
    hence "Col B C' C" 
      by (metis \<open>Col A' B C'\<close> assms(2) assms(4) col_transitivity_2)
    hence "Bet A B C" 
      using \<open>A = A'\<close> assms(1) assms(3) assms(6) l8_9 by blast
  }
  moreover 
  {
    assume "A \<noteq> A'"
    {
      assume "C = C'"
      hence "Col B A' A" 
        using \<open>Col A' B C'\<close> assms(3) assms(4) l6_16_1 not_col_permutation_2 by blast
      hence False 
        using \<open>A \<noteq> A'\<close> assms(2) assms(5) l8_9 by blast
    }
    hence "C \<noteq> C'" 
      by blast
    hence "\<not> Col C' C B" 
      using Col_cases assms(3) assms(6) l8_9 by blast
    hence "C C' OS B A'" 
      using assms(1) assms(3) bet_out_1 
        invert_one_side out_one_side by presburger
    have "B A' Perp A' A" 
      using \<open>A \<noteq> A'\<close> assms(2) assms(5) per_perp by auto
    have "B C' Perp C' C" 
      using \<open>C \<noteq> C'\<close> assms(3) assms(6) per_perp by auto
    have "A A' Par C C'" 
    proof (rule l12_9 [where ?C1.0="B" and ?C2.0="A'"])
      show "Coplanar B A' A C" 
        using Col_cases assms(4) ncop__ncols by blast
      show "Coplanar B A' A C'" 
        using Col_cases \<open>Col A' B C'\<close> ncop__ncols by blast
      show "Coplanar B A' A' C" 
        using ncop_distincts by blast
      show "Coplanar B A' A' C'" 
        using ncop_distincts by blast
      show "A A' Perp B A'" 
        using Perp_perm \<open>B A' Perp A' A\<close> by blast
      show "C C' Perp B A'" 
        using Perp_cases \<open>B C' Perp C' C\<close> \<open>Col A' B C'\<close> assms(2) 
          col_permutation_1 perp_col1 by blast
    qed
    {
      assume "A A' ParStrict C C'"
      hence "C C' ParStrict A A'" 
        by (simp add: par_strict_symmetry)
      have "A A' OS C C'" 
        by (simp add: \<open>C C' ParStrict A A'\<close> pars__os3412)
      have "C C' OS A A'" 
        using \<open>A A' ParStrict C C'\<close> pars__os3412 by blast
      have "\<not> Col A' A B" 
        using Col_cases \<open>A \<noteq> A'\<close> assms(2) assms(5) l8_9 by blast
      hence "A' A OS B C'" 
        by (simp add: assms(1) assms(2) bet_out out_one_side)
      have "A' A OS B C" 
        using Par_strict_cases \<open>A A' ParStrict C C'\<close> \<open>A' A OS B C'\<close> 
          l12_6 one_side_transitivity by blast
      hence "A Out B C" 
        using assms(4) col_one_side_out invert_one_side by blast
      have "C C' OS B A" 
        using \<open>C C' OS A A'\<close> \<open>C C' OS B A'\<close> one_side_symmetry one_side_transitivity by blast
      hence "C Out B A" 
        using Col_perm assms(4) col_one_side_out by blast
      have "Bet A C B \<longrightarrow> False" 
        using \<open>C Out B A\<close> l6_6 not_bet_and_out by blast
      moreover have "Bet C A B \<longrightarrow> False" 
        using Bet_cases \<open>A Out B C\<close> not_bet_and_out by blast
      ultimately have "Bet A B C" 
        using assms(4) third_point by blast
    }
    moreover {
      assume "A \<noteq> A'" and "C \<noteq> C'" and "Col A C C'" and "Col A' C C'"
      have "A' C' Perp A A'"
      proof (rule perp_col [where ?B = "B"], simp_all add: \<open>Col A' B C'\<close>)
        show "A' \<noteq> C'" 
          using assms(1) assms(3) between_identity by blast
        show "A' B Perp A A'"  
          by (simp add: \<open>B A' Perp A' A\<close> perp_comm)
      qed
      hence "Bet A B C" 
        using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
          per13_preserves_bet_inv by blast
    }
    ultimately have "Bet A B C" 
      using Par_def \<open>A A' Par C C'\<close> by force
  }
  ultimately show ?thesis
    by blast
qed

lemma l13_10_aux3:
  assumes "\<not> Col PO A A'" and
    "B \<noteq> PO" and
    "C \<noteq> PO" and
    "Col PO A B" and
    "Col PO B C" and
    "B' \<noteq> PO" and
    "C' \<noteq> PO" and
    "Col PO A' B'" and
    "Col PO B' C'" and
    "PO Perp2 B C' C B'" and
    "PO Perp2 C A' A C'" and
    "Bet A PO B" 
  shows "Bet A' PO B'" 
proof -
  have "A \<noteq> PO" 
    using assms(1) col_trivial_1 by fastforce
  have "A' \<noteq> PO" 
    using assms(1) not_col_distincts by blast
  have "Col PO A C" 
    by (metis assms(2) assms(4) assms(5) col_trivial_3 colx)
  have "Col PO A' C'" 
    by (metis assms(6) assms(8) assms(9) col_trivial_3 colx)  
  have "Bet C A PO \<or> Bet A C PO \<or> Bet PO C B \<or> Bet PO B C" 
    by (metis NCol_perm \<open>Col PO A C\<close> assms(12) fourth_point not_bet_distincts)
  moreover 
  {
    assume "Bet C A PO"
    have "Bet PO C' A'"
    proof (rule perp2_preserves_bet23 [where ?A = "A" and ?B = "C"])
      show "Bet PO A C" 
        using Bet_cases \<open>Bet C A PO\<close> by blast
      show "Col PO C' A'"           
        using \<open>Col PO A' C'\<close> not_col_permutation_5 by blast
      show "\<not> Col PO A C'"           
        by (metis \<open>Col PO C' A'\<close> assms(1) assms(7) col_trivial_3 colx)
      show "PO Perp2 A C' C A'" 
        by (simp add: assms(11) perp2_sym)
    qed
    moreover have "Bet B' PO C'" 
    proof (rule perp2_preserves_bet13 [where ?B="B" and ?C="C"])
      show "Bet B PO C" 
        using \<open>A \<noteq> PO\<close> \<open>Bet C A PO\<close> assms(12) between_symmetry 
          outer_transitivity_between2 by blast
      show "Col PO B' C'" 
        by (simp add: assms(9))
      show "\<not> Col PO B B'" 
        by (metis assms(1) assms(2) assms(4) assms(6) assms(8) col_trivial_3 
            colx not_col_permutation_5)
      show "PO Perp2 B C' C B'" 
        using assms(10) by auto
    qed
    ultimately have "Bet A' PO B'" 
      using assms(7) between_symmetry outer_transitivity_between by blast
  }
  moreover 
  {
    assume "Bet A C PO" 
    have "Bet PO A' C'" 
      by (metis \<open>Bet A C PO\<close> \<open>Col PO A' C'\<close> assms(1) assms(11) assms(3) 
          bet_col between_symmetry col_transitivity_1 perp2_preserves_bet23)
    moreover have "Bet B' PO C'"
    proof (rule perp2_preserves_bet13 [where ?B = "B" and ?C = "C"], 
        simp_all add: assms(9) assms(10))
      have "Bet C PO B" 
        using \<open>Bet A C PO\<close> assms(12) between_exchange3 by blast
      thus "Bet B PO C" 
        using Bet_cases by blast
      show "\<not> Col PO B B'" 
        by (metis assms(1) assms(2) assms(4) assms(6) assms(8) 
            colx not_col_distincts not_col_permutation_2)
    qed
    ultimately have "Bet A' PO B'" 
      using between_inner_transitivity between_symmetry by blast
  }
  moreover 
  {
    assume "Bet PO C B"
    have "Bet A PO C" 
      using \<open>Bet PO C B\<close> assms(12) between_inner_transitivity by blast
    have "Bet PO B' C'" 
      by (metis \<open>Bet PO C B\<close> \<open>Col PO A C\<close> assms(1) assms(10) assms(3) assms(6) 
          assms(8) assms(9) colx not_col_distincts not_col_permutation_5 
          perp2_preserves_bet23 perp2_sym)
    have "Bet C' PO A'" 
    proof (rule perp2_preserves_bet13 [where ?B = "C" and ?C = "A"])
      show "Bet C PO A" 
        by (simp add: \<open>Bet A PO C\<close> between_symmetry)
      show "Col PO C' A'" 
        using \<open>Col PO A' C'\<close> not_col_permutation_5 by blast
      show "\<not> Col PO C C'" 
        by (metis \<open>Col PO A C\<close> \<open>Col PO C' A'\<close> assms(1) assms(3) assms(7) col_trivial_3 colx)
      show "PO Perp2 C A' A C'" 
        using assms(11) by auto
    qed
    have "Bet A' PO B'" 
      using \<open>Bet C' PO A'\<close> \<open>Bet PO B' C'\<close> between_exchange3 between_symmetry by blast
  }
  moreover 
  {
    assume "Bet PO C B"
    hence "Bet A PO C" 
      using \<open>Bet PO C B\<close> assms(12) between_inner_transitivity by blast
    moreover have "Bet PO B' C'" 
    proof (rule perp2_preserves_bet23 [where ?A = "C" and ?B = "B"])
      show "Bet PO C B" 
        by (simp add: \<open>Bet PO C B\<close>)
      show "Col PO B' C'" 
        by (simp add: assms(9))
      show "\<not> Col PO C B'" 
        by (metis \<open>Col PO A C\<close> assms(1) assms(3) assms(6) assms(8) col_trivial_3 colx 
            not_col_permutation_5)
      show "PO Perp2 C B' B C'" 
        by (simp add: assms(10) perp2_sym)
    qed
    moreover have "Bet C' PO A'" 
      using \<open>Bet A PO C\<close> \<open>Col PO A' C'\<close> assms(1) assms(11) between_symmetry 
        perp2_preserves_bet13 perp2_sym by blast
    ultimately have "Bet A' PO B'" 
      using \<open>Bet PO C B \<Longrightarrow> Bet A' PO B'\<close> \<open>Bet PO C B\<close> by blast
  }
  ultimately show ?thesis 
    by (metis \<open>Col PO A C\<close> \<open>Col PO A' C'\<close> assms(1) assms(10) assms(11) assms(2) 
        assms(4) assms(7) assms(9) between_symmetry colx not_col_distincts 
        not_col_permutation_5 outer_transitivity_between perp2_preserves_bet13 
        perp2_preserves_bet23 third_point)
qed

lemma l13_10_aux4:
  assumes "\<not> Col PO A A'" and
    "B \<noteq> PO" and
    "C \<noteq> PO" and
    "Col PO A B" and
    "Col PO B C" and
    "B' \<noteq> PO" and
    "C' \<noteq> PO" and
    "Col PO A' B'" and
    "Col PO B' C'" and
    "PO Perp2 B C' C B'" and
    "PO Perp2 C A' A C'" and
    "Bet PO A B"
  shows "PO Out A' B'" 
proof -
  have "A \<noteq> PO" 
    using assms(1) not_col_distincts by blast
  have "A' \<noteq> PO" 
    using assms(1) not_col_distincts by blast
  have "Col PO A C" 
    by (metis assms(2) assms(4) assms(5) col_trivial_3 colx)
  {
    assume "A = B"
    have "\<not> Col A C' PO" 
      by (metis assms(1) assms(6) assms(7) assms(8) assms(9) col2__eq 
          col_permutation_4 col_permutation_5)
    have "PO Perp2 C A' C B'"
    proof (rule perp2_pseudo_trans [where ?C = "C" and ?D = "B'"])
      show "PO Perp2 C A' C B'" 
        using \<open>A = B\<close> \<open>\<not> Col A C' PO\<close> assms(10) assms(11) perp2_pseudo_trans by blast
      show "PO Perp2 C B' C B'" 
        by (metis \<open>A = B\<close> assms(1) assms(5) assms(6) assms(8) 
            col_transitivity_2 not_col_permutation_1 perp2_refl)
      show "\<not> Col C B' PO" 
        by (metis \<open>A = B\<close> assms(1) assms(3) assms(5) assms(6) assms(8) col2__eq 
            col_permutation_4 col_permutation_5)
    qed
    have "C A' Par C B'" 
      by (metis \<open>Col PO A C\<close> \<open>PO Perp2 C A' C B'\<close> assms(1) assms(6) assms(8) 
          between_equality_2 between_trivial col_transitivity_1 not_col_permutation_5 
          not_par_not_col par_reflexivity perp2_preserves_bet23 perp2_sym)
    have "A' = B'" 
      using \<open>A = B\<close> \<open>C A' Par C B'\<close> assms(1) assms(3) assms(5) assms(8)
        col_trivial_3 l6_21 not_col_permutation_2 par_id_2 by blast
    hence ?thesis 
      using assms(6) out_trivial by blast
  }
  moreover 
  {
    assume "A \<noteq> B"
    have "Bet C PO A \<or> Bet PO C A \<or> Bet A C B \<or> Bet A B C" 
      using \<open>A \<noteq> B\<close> \<open>A \<noteq> PO\<close> \<open>Col PO A C\<close> assms(12) fourth_point by auto
    moreover 
    {
      assume "Bet C PO A"
      have "Bet C PO B" 
        using \<open>A \<noteq> PO\<close> \<open>Bet C PO A\<close> assms(12) outer_transitivity_between by blast
      hence "Bet B' PO C'" 
        by (metis Col_cases assms(1) assms(10) assms(2) assms(4) 
            assms(6) assms(8) assms(9) between_symmetry col2__eq perp2_preserves_bet13)
      moreover have "Bet A' PO C'" 
        by (metis \<open>Bet C PO A\<close> assms(1) assms(11) assms(6) assms(8) 
            assms(9) between_symmetry col_not_col_not_par not_col_distincts 
            not_par_not_col perp2_preserves_bet13 perp2_sym)
      ultimately have ?thesis 
        using \<open>A' \<noteq> PO\<close> assms(6) assms(7) l6_2 by blast
    }
    moreover 
    {
      assume "Bet PO C A"
      hence "Bet PO C B" 
        using assms(12) between_exchange4 by blast
      have "Bet PO B' C'"
      proof (rule perp2_preserves_bet23 [where ?A = "C" and ?B = "B"])
        show "Bet PO C B" 
          using \<open>Bet PO C B\<close> by auto
        show "Col PO B' C'" 
          by (simp add: assms(9))
        show "\<not> Col PO C B'" 
          by (metis (full_types) \<open>Col PO A C\<close> assms(1) assms(3) assms(6) 
              assms(8) colx l6_16_1 not_col_permutation_5)
        show "PO Perp2 C B' B C'" 
          by (simp add: assms(10) perp2_sym)
      qed
      moreover have "Bet PO A' C'" 
        by (metis \<open>Bet PO C A\<close> \<open>Col PO A C\<close> assms(1) assms(11) assms(3) assms(6) 
            assms(8) assms(9) colx not_col_distincts perp2_preserves_bet23)
      ultimately have ?thesis 
        using \<open>A' \<noteq> PO\<close> assms(6) bet2__out by force
    }
    moreover 
    {
      assume "Bet A C B"
      have "Bet PO A C" 
        using \<open>Bet A C B\<close> assms(12) between_inner_transitivity by blast
      have "Bet PO C' A'"
      proof (rule perp2_preserves_bet23 [where ?A = "A" and ?B = "C"])
        show "Bet PO A C" 
          by (simp add: \<open>Bet PO A C\<close>)
        show "Col PO C' A'" 
          by (metis Col_cases assms(6) assms(8) assms(9) col_transitivity_1)
        show "\<not> Col PO A C'" 
          by (metis \<open>Col PO C' A'\<close> assms(1) assms(7) col_trivial_3 colx)
        show "PO Perp2 A C' C A'"
          by (simp add: assms(11) perp2_sym)
      qed
      have "Bet PO C B" 
        using \<open>Bet A C B\<close> assms(12) between_exchange2 by blast
      have "Bet PO B' C'" 
      proof (rule perp2_preserves_bet23 [where ?A = "C" and ?B = "B"])
        show "Bet PO C B" 
          by (simp add: \<open>Bet PO C B\<close>)
        show "Col PO B' C'" 
          by (simp add: assms(9))
        {
          assume "Col PO C B'"
          have False 
            by (metis \<open>Col PO A C\<close> \<open>Col PO C B'\<close> assms(1) assms(3) assms(6) 
                assms(8) col_transitivity_1 not_col_permutation_5)          
        }
        thus "\<not> Col PO C B'" 
          by blast
        show "PO Perp2 C B' B C'"
          by (simp add: assms(10) perp2_sym)
      qed
      hence ?thesis 
        by (meson Out_def \<open>A' \<noteq> PO\<close> \<open>Bet PO C' A'\<close> assms(6) between_exchange4)
    }
    moreover 
    {
      assume "Bet A B C"
      have "Bet PO A C" 
        using \<open>A \<noteq> B\<close> \<open>Bet A B C\<close> assms(12) outer_transitivity_between by blast
      have "Bet PO B C"
        using \<open>Bet A B C\<close> \<open>Bet PO A C\<close> between_exchange2 by blast
      have "Bet PO C' B'" 
      proof (rule perp2_preserves_bet23 [where ?A="B" and ?B="C"])
        show "Bet PO B C" 
          by (simp add: \<open>Bet PO B C\<close>)
        show "Col PO C' B'" 
          using Col_cases assms(9) by blast
        {
          assume "Col PO B C'"
          hence "Col PO A A'" 
            by (metis \<open>Col PO C' B'\<close> assms(2) assms(4) assms(6) assms(7) assms(8) 
                col_permutation_5 col_transitivity_1)
          hence False 
            using assms(1) by blast
        }
        thus "\<not> Col PO B C'" 
          by blast
        show "PO Perp2 B C' C B'" 
          by (simp add: assms(10))
      qed
      have "Bet PO C' A'" 
      proof (rule perp2_preserves_bet23 [where ?A="A" and ?B="C"])
        show "Bet PO A C" 
          by (simp add: \<open>Bet PO A C\<close>)
        show "Col PO C' A'" 
          by (metis assms(6) assms(8) assms(9) col_permutation_5 col_trivial_3 colx)
        show "\<not> Col PO A C'" 
          by (metis \<open>Col PO C' A'\<close> assms(1) assms(7) col_trivial_3 colx)
        show "PO Perp2 A C' C A'" 
          by (simp add: assms(11) perp2_sym)
      qed
      hence ?thesis 
        by (metis Out_def \<open>Bet PO C' B'\<close> assms(7) bet_out l5_1)
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma l13_10_aux5:
  assumes "\<not> Col PO A A'" and
    "B \<noteq> PO" and
    "C \<noteq> PO" and
    "Col PO A B" and
    "Col PO B C" and
    "B' \<noteq> PO" and
    "C' \<noteq> PO" and
    "Col PO A' B'" and
    "Col PO B' C'" and
    "PO Perp2 B C' C B'" and
    "PO Perp2 C A' A C'" and
    "PO Out A B" 
  shows "PO Out A' B'" 
proof -
  have "A' \<noteq> PO" 
    using assms(1) not_col_distincts by blast
  have "A \<noteq> PO" 
    using Out_def assms(12) by blast
  have "B \<noteq> PO" 
    using assms(2) by auto
  have "Bet PO A B \<or> Bet PO B A" 
    using Out_def assms(12) by force
  moreover have "Bet PO A B \<longrightarrow> ?thesis" 
    using assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) assms(5) 
      assms(6) assms(7) assms(8) assms(9) l13_10_aux4 by blast
  moreover 
  {
    assume "Bet PO B A"
    have "PO Out B' A'"
    proof (rule l13_10_aux4 [where ?A = "B" and ?B = "A" and ?C = "C" and ?C'= "C'"])
      show "\<not> Col PO B B'" 
        by (metis assms(1) assms(2) assms(4) assms(6) assms(8) col_trivial_3 
            colx not_col_permutation_5)
      show "A \<noteq> PO" 
        by (simp add: \<open>A \<noteq> PO\<close>)
      show "C \<noteq> PO" 
        by (simp add: assms(3))
      show "Col PO B A" 
        using Col_cases assms(4) by blast
      show "Col PO A C" 
        by (metis \<open>Col PO B A\<close> assms(2) assms(5) col_transitivity_1)
      show "A' \<noteq> PO" 
        by (simp add: \<open>A' \<noteq> PO\<close>)
      show "C' \<noteq> PO" 
        by (simp add: assms(7))
      show "Col PO B' A'" 
        using assms(8) not_col_permutation_5 by blast
      show "Col PO A' C'" 
        by (metis \<open>Col PO B' A'\<close> assms(6) assms(9) col_transitivity_1)
      show "PO Perp2 A C' C A'" 
        by (simp add: assms(11) perp2_sym)
      show "PO Perp2 C B' B C'" 
        by (simp add: assms(10) perp2_sym)
      show "Bet PO B A" 
        by (simp add: \<open>Bet PO B A\<close>)
    qed
    hence ?thesis 
      using l6_6 by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma cop_per2__perp_aux:
  assumes "A \<noteq> B" and
    "X \<noteq> Y" and
    "B \<noteq> X" and
    "Coplanar A B X Y" and
    "Per A B X" and
    "Per A B Y"
  shows "A B Perp X Y" 
proof -
  have "B B Perp B X \<longrightarrow> A B Perp X Y" 
    using perp_distinct by blast
  moreover
  {
    assume "A B Perp B X"
    hence "X B Perp A B" 
      using Perp_cases by blast
    have "Col X Y B"
    proof (rule cop_per2__col [where ?A = "A"])
      show "Coplanar A X Y B" 
        using assms(4) coplanar_perm_3 by blast
      show "A \<noteq> B" 
        by (simp add: assms(1))
      show "Per X B A" 
        by (simp add: assms(5) l8_2)
      show "Per Y B A" 
        by (simp add: assms(6) l8_2)
    qed
    have "X Y Perp A B" 
      using perp_col [where ?B = "B"] 
      by (meson Col_cases \<open>Col X Y B\<close> \<open>X B Perp A B\<close> assms(2))
    hence "A B Perp X Y" 
      using Perp_cases by blast
  }
  ultimately show ?thesis 
    using \<open>B \<noteq> X\<close> assms(1) assms(5) per_perp by blast
qed

lemma cop_per2__perp:
  assumes "A \<noteq> B" and
    "X \<noteq> Y" and
    "B \<noteq> X \<or> B \<noteq> Y" and
    "Coplanar A B X Y" and
    "Per A B X" and
    "Per A B Y"
  shows "A B Perp X Y" 
proof -
  have "B \<noteq> X \<longrightarrow> ?thesis" 
    by (simp add: assms(1) assms(2) assms(4) assms(5) assms(6) cop_per2__perp_aux)
  moreover hence "B \<noteq> Y \<longrightarrow> ?thesis" 
    using cop_per2__perp_aux assms(1) assms(6) per_perp by force
  ultimately show ?thesis 
    using assms(3) by blast
qed

lemma l13_10:
  assumes "\<not> Col PO A A'" and
    "B \<noteq> PO" and 
    "C \<noteq> PO" and
    "Col PO A B" and 
    "Col PO B C" and
    "B' \<noteq> PO" and
    "C' \<noteq> PO" and
    "Col PO A' B'" and
    "Col PO B' C'" and
    "PO Perp2 B C' C B'" and
    "PO Perp2 C A' A C'"
  shows "PO Perp2 A B' B A'" 
proof -
  have "Col PO A C" 
    by (metis assms(2) assms(4) assms(5) col_trivial_3 colx)
  have "Col PO A' C'" 
    by (metis assms(6) assms(8) assms(9) col_trivial_3 colx)
  have "A \<noteq> PO" 
    using assms(1) not_col_distincts by auto
  have "\<not> Col A B' PO" 
    by (meson assms(1) assms(6) assms(8) col_trivial_3 colx 
        not_col_permutation_3 not_col_permutation_5)
  have "\<exists> P Q. Col B C' P \<and> Col C B' Q \<and> Col PO P Q \<and> 
                P PerpAt PO P B C' \<and> Q PerpAt PO Q C B'"
  proof (rule perp2_perp_in)
    show "PO Perp2 B C' C B'" 
      by (simp add: assms(10))
    show "\<not> Col PO B C'" 
      by (metis NCol_perm \<open>Col PO A' C'\<close> assms(1) assms(2) assms(4) 
          assms(7) colx not_col_distincts)
    show "\<not> Col PO C B'" 
      by (meson \<open>Col PO A C\<close> \<open>\<not> Col A B' PO\<close> assms(3) col_trivial_3 colx 
          not_col_permutation_3 not_col_permutation_5)
  qed
  then obtain L L' where "Col B C' L" and "Col C B' L'" and 
    "Col PO L L'" and "L PerpAt PO L B C'" and "L' PerpAt PO L' C B'"
    by blast
  have "\<exists> P Q. Col C A' P \<and> Col A C' Q \<and> Col PO P Q \<and>
P PerpAt PO P C A' \<and> Q PerpAt PO Q A C'" 
  proof (rule perp2_perp_in)
    show "PO Perp2 C A' A C'" 
      by (simp add: assms(11))
    show "\<not> Col PO C A'" 
      by (metis \<open>Col PO A C\<close> assms(1) assms(3) col_trivial_3 colx)
    show "\<not> Col PO A C'" 
      using NCol_perm \<open>Col PO A' C'\<close> assms(1) assms(7) col_trivial_3 colx by blast
  qed
  then obtain M M' where "Col C A' M" and "Col A C' M'" and 
    "Col PO M M'" and "M PerpAt PO M C A'" and "M' PerpAt PO M' A C'"  
    by blast
  obtain N where "Col A B' N" and "A B' Perp PO N" 
    using l8_18_existence \<open>\<not> Col A B' PO\<close> by blast
  have "Col PO PO N" 
    using col_trivial_1 by auto
  moreover have "PO N Perp A B'" 
    using Perp_perm \<open>A B' Perp PO N\<close> by blast
  moreover have "PO N Perp B A'" 
  proof -
    obtain la where "QCong la" and "la PO A" 
      using lg_exists by blast
    obtain lb where "QCong lb" and "lb PO B" 
      using lg_exists by blast
    obtain lc where "QCong lc" and "lc PO C" 
      using lg_exists by blast
    obtain la' where "QCong la'" and "la' PO A'" 
      using lg_exists by blast
    obtain lb' where "QCong lb'" and "lb' PO B'" 
      using lg_exists by blast
    obtain lc' where "QCong lc'" and "lc' PO C'" 
      using lg_exists by blast
    obtain ll where "QCong ll" and "ll PO L" 
      using lg_exists by blast
    obtain ll' where "QCong ll'" and "ll' PO L'" 
      using lg_exists by blast
    obtain lm where "QCong lm" and "lm PO M" 
      using lg_exists by blast
    obtain lm' where "QCong lm'" and "lm' PO M'" 
      using lg_exists by blast
    obtain ln where "QCong ln" and "ln PO N" 
      using lg_exists by blast
    have "PO \<noteq> L" 
      using \<open>L PerpAt PO L B C'\<close> perp_in_distinct by auto
    have "PO \<noteq> L'" 
      using \<open>L' PerpAt PO L' C B'\<close> perp_in_distinct by auto
    have "\<not> Col PO B B'" 
      by (meson \<open>\<not> Col A B' PO\<close> assms(2) assms(4) col_permutation_1 col_trivial_3 colx)
    have "\<not> Col PO C C'" 
      by (meson \<open>Col PO A C\<close> \<open>\<not> Col A B' PO\<close> assms(3) assms(7) assms(9) 
          col_transitivity_2 not_col_permutation_1)
    have "\<exists> a. QCongAAcute a \<and> Lcos ll lb a \<and> Lcos ll' lc a" 
    proof (cases "B = L")
      case True
      hence "B' \<noteq> L'" 
        using \<open>Col PO L L'\<close> \<open>\<not> Col PO B B'\<close> by auto
      hence "C = L'" 
        by (metis Col_cases True \<open>Col C B' L'\<close> \<open>Col PO L L'\<close> \<open>\<not> Col PO B B'\<close> assms(5) colx)
      thus ?thesis
        using True \<open>Col PO L L'\<close> \<open>PO \<noteq> L'\<close> \<open>QCong lb\<close> \<open>QCong lc\<close> \<open>QCong ll'\<close> 
          \<open>QCong ll\<close> \<open>lb PO B\<close> \<open>lc PO C\<close> \<open>ll PO L\<close> \<open>ll' PO L'\<close> assms(2) l13_10_aux2 by auto
    next
      case False
      have "PO L Perp L B" 
        by (meson False \<open>L PerpAt PO L B C'\<close> l8_15_2 perp_in_col 
            perp_in_col_perp_in perp_right_comm)
      moreover have "PO L' Perp L' C" 
        by (metis \<open>Col C B' L'\<close> \<open>Col PO L L'\<close> \<open>L' PerpAt PO L' C B'\<close> assms(5)
            calculation col_transitivity_2 not_col_distincts perp_col1 
            perp_in_perp perp_not_col2 perp_right_comm)
      ultimately show ?thesis 
        using l13_10_aux1 
        using \<open>Col PO L L'\<close> \<open>QCong lb\<close> \<open>QCong lc\<close> \<open>QCong ll'\<close> \<open>QCong ll\<close> 
          \<open>lb PO B\<close> \<open>lc PO C\<close> \<open>ll PO L\<close> \<open>ll' PO L'\<close> assms(5) by auto
    qed
    then obtain l' where "QCongAAcute l'" and "Lcos ll lb l'" and "Lcos ll' lc l'" 
      by blast
    have "\<exists> a. QCongAAcute a \<and> Lcos ll lc' a \<and> Lcos ll' lb' a" 
    proof (cases "C' = L")
      case True
      have "C \<noteq> L'" 
        using \<open>\<not> Col PO C C'\<close> True \<open>Col PO L L'\<close> not_col_permutation_5 by blast
      hence "B' = L'" 
        using l6_21 by (metis True \<open>Col C B' L'\<close> \<open>Col PO L L'\<close> \<open>\<not> Col PO C C'\<close> 
            assms(9) col_transitivity_1 not_col_distincts)
      thus ?thesis 
        using l13_10_aux2 [where ?PO = "PO" and ?A = "A" and ?B = "B"]
        by (metis True \<open>QCong lb'\<close> \<open>QCong lc'\<close> \<open>QCong ll'\<close> \<open>QCong ll\<close> 
            \<open>lb' PO B'\<close> \<open>lc' PO C'\<close> \<open>ll PO L\<close> \<open>ll' PO L'\<close> assms(6) 
            assms(7) assms(9) l13_10_aux2)
    next
      case False
      show ?thesis 
      proof (rule l13_10_aux1 [where ?PO="PO" and ?A="C'" and ?B="B'" and ?P="L" and ?Q="L'"],
          simp_all add: \<open>Col PO L L'\<close> \<open>QCong lc'\<close> \<open>QCong lb'\<close> \<open>QCong ll\<close> \<open>QCong ll'\<close>
          \<open>lc' PO C'\<close>\<open>lb' PO B'\<close>\<open>ll PO L\<close>\<open>ll' PO L'\<close>)
        show "Col PO C' B'" 
          using Col_cases assms(9) by auto
        show "PO L Perp L C'" 
          by (metis False \<open>Col B C' L\<close> \<open>L PerpAt PO L B C'\<close> col_permutation_5 
              col_transitivity_1 perp_col2_bis perp_in_perp)
        show "PO L' Perp L' B'" 
          by (metis \<open>Col C B' L'\<close> \<open>Col PO L L'\<close> \<open>L' PerpAt PO L' C B'\<close> 
              \<open>PO L Perp L C'\<close> assms(9) col_transitivity_2 not_col_permutation_1 
              perp_col2_bis perp_in_perp perp_not_col2)
      qed
    qed
    then obtain l where "QCongAAcute l" and "Lcos ll lc' l" and "Lcos ll' lb' l" 
      by blast
    have "\<exists> a. QCongAAcute a \<and> Lcos lm lc a \<and> Lcos lm' la a" 
    proof (cases "C = M")
      case True
      have "A = M'"
      proof (rule l6_21 [where ?A="PO" and ?B="C" and ?C="C'" and ?D="M'"])
        show "\<not> Col PO C C'" 
          using \<open>\<not> Col PO C C'\<close> by blast
        {
          assume "C' = M'" 
          hence False 
            using True \<open>Col PO M M'\<close> \<open>\<not> Col PO C C'\<close> by blast
        }
        thus "C' \<noteq> M'" 
          by blast
        show "Col PO C A" 
          using Col_cases \<open>Col PO A C\<close> by blast
        show "Col PO C M'" 
          by (simp add: True \<open>Col PO M M'\<close>)
        show "Col C' M' A" 
          using Col_cases \<open>Col A C' M'\<close> by blast
        show "Col C' M' M'" 
          by (simp add: col_trivial_2)
      qed
      show ?thesis 
      proof (rule l13_10_aux2 [where ?PO="PO" and ?A="C" and ?B="A"],
          simp_all add: \<open>QCong lc\<close> \<open>QCong lm\<close> \<open>QCong lm'\<close> \<open>QCong la\<close> 
          \<open>lc PO C\<close> \<open>la PO A\<close> assms(3) \<open>A \<noteq> PO\<close>)
        show "Col PO C A" 
          by (simp add: True \<open>A = M'\<close> \<open>Col PO M M'\<close>)
        show "lm PO C" 
          by (simp add: True \<open>lm PO M\<close>)
        show "lm' PO A" 
          by (simp add: \<open>A = M'\<close> \<open>lm' PO M'\<close>)
      qed
    next
      case False
      hence "C \<noteq> M" 
        by blast
      have "PO M Perp M C" 
        using False \<open>Col C A' M\<close> \<open>M PerpAt PO M C A'\<close> col_trivial_3 
          perp_col2_bis perp_in_perp by blast
      moreover have "PO M' Perp M' A" 
        by (metis \<open>Col A C' M'\<close> \<open>Col PO A C\<close> \<open>Col PO M M'\<close> \<open>M' PerpAt PO M' A C'\<close> 
            calculation col3 not_col_distincts perp_col1 perp_in_perp 
            perp_not_col2 perp_right_comm)
      ultimately show ?thesis 
        using l13_10_aux1 by (metis \<open>Col PO A C\<close> \<open>Col PO M M'\<close> \<open>QCong la\<close> 
            \<open>QCong lc\<close> \<open>QCong lm'\<close> \<open>QCong lm\<close> \<open>la PO A\<close> \<open>lc PO C\<close> \<open>lm PO M\<close> 
            \<open>lm' PO M'\<close> not_col_permutation_5) 
    qed
    then obtain m' where "QCongAAcute m'" and "Lcos lm lc m'" and "Lcos lm' la m'" 
      by blast 
    have "\<exists> a. QCongAAcute a \<and> Lcos lm la' a \<and> Lcos lm' lc' a" 
    proof (cases "A' = M")
      case True
      have "C' = M'" 
      proof (rule l6_21 [where ?A="PO" and ?B="A'" and ?C="A" and ?D="M'"])
        show "\<not> Col PO A' A" 
          using assms(1) not_col_permutation_5 by blast
        show "A \<noteq> M'" 
          using Col_cases True \<open>Col PO M M'\<close> assms(1) by blast
        show "Col PO A' C'" 
          by (simp add: \<open>Col PO A' C'\<close>)
        show "Col PO A' M'" 
          by (simp add: True \<open>Col PO M M'\<close>)
        show "Col A M' C'" 
          using Col_cases \<open>Col A C' M'\<close> by blast
        show "Col A M' M'" 
          by (simp add: col_trivial_2)
      qed
      show ?thesis
      proof (rule l13_10_aux2 [where PO="PO" and ?A="A'" and ?B="C'"],
          simp_all add:  \<open>QCong la'\<close> \<open>QCong lc'\<close> \<open>QCong lm\<close> \<open>QCong lm'\<close> 
          assms(7) \<open>Col PO A' C'\<close> \<open>la' PO A'\<close> \<open>lc' PO C'\<close>)
        show "lm PO A'" 
          by (simp add: True \<open>lm PO M\<close>)
        show "lm' PO C'" 
          using \<open>C' = M'\<close> \<open>lm' PO M'\<close> by auto
        show "A' \<noteq> PO" 
          using assms(1) col_trivial_3 by blast
      qed
    next
      case False 
      hence "A' \<noteq> M" 
        by simp
      have "PO M Perp M A'" 
        using False \<open>Col C A' M\<close> \<open>M PerpAt PO M C A'\<close> col_trivial_2 
          perp_col2_bis perp_in_perp by blast
      moreover have "PO M' Perp M' C'" 
        by (metis \<open>Col A C' M'\<close> \<open>Col PO M M'\<close> \<open>M' PerpAt PO M' A C'\<close> assms(6) 
            assms(8) assms(9) calculation col_transitivity_1 not_col_distincts 
            perp_col2_bis perp_in_perp perp_not_col2)
      ultimately show ?thesis
        using l13_10_aux1 [where ?PO="PO" and ?A="A'" and ?B="C'" and ?P="M" and ?Q="M'"]
        by (simp add: \<open>Col PO A' C'\<close> \<open>Col PO M M'\<close> \<open>QCong la'\<close> \<open>QCong lc'\<close> 
            \<open>QCong lm'\<close> \<open>QCong lm\<close> \<open>la' PO A'\<close> \<open>lc' PO C'\<close> \<open>lm PO M\<close> \<open>lm' PO M'\<close>)
    qed
    then obtain m where "QCongAAcute m" and "Lcos lm la' m" and "Lcos lm' lc' m"
      by blast
    have "\<exists> a. QCongAAcute a \<and> Lcos ln la a" 
    proof -
      have "\<exists> a. QCongAAcute a \<and> a A PO N" 
      proof (rule anga_exists,simp_all add:\<open>A \<noteq> PO\<close>)
        show "N \<noteq> PO" 
          using \<open>Col A B' N\<close> \<open>\<not> Col A B' PO\<close> by auto
        show "Acute A PO N" 
          by (meson \<open>Col A B' N\<close> calculation(2) l8_14_2_1b_bis not_col_distincts
              not_col_permutation_1 perp_acute)
      qed
      then obtain n' where "QCongAAcute n'" and "n' A PO N" 
        by blast
      have "Per A N PO" 
        by (meson \<open>A B' Perp PO N\<close> \<open>Col A B' N\<close> l8_16_1 l8_2 not_col_distincts)
      hence "Lcos ln la n'" 
        by (metis Lcos_def \<open>QCong la\<close> \<open>QCong ln\<close> \<open>QCongAACute n'\<close> 
            \<open>la PO A\<close> \<open>ln PO N\<close> \<open>n' A PO N\<close> anga_sym)
      thus ?thesis
        using \<open>QCongAACute n'\<close> by blast
    qed
    then obtain n' where "QCongAAcute n'" and "Lcos ln la n'" 
      by blast
    have "\<exists> a. QCongAAcute a \<and> Lcos ln lb' a" 
    proof -
      have "\<exists> a. QCongAAcute a \<and> a B' PO N" 
      proof (rule anga_exists, simp add: assms(6))
        show "N \<noteq> PO" 
          using \<open>Col A B' N\<close> \<open>\<not> Col A B' PO\<close> by blast
        show "Acute B' PO N" 
        proof (cases "B' = N")
          case True
          thus ?thesis
            using \<open>N \<noteq> PO\<close> acute_trivial by auto
        next
          case False
          show ?thesis
          proof (rule perp_acute [where ?C = "N"])
            show "Col B' N N" 
              using col_trivial_2 by auto
            show "N PerpAt PO N B' N" 
              by (meson False \<open>A B' Perp PO N\<close> \<open>Col A B' N\<close> l8_15_1 not_col_permutation_4 
                  perp_in_col_perp_in perp_in_left_comm perp_in_sym)
          qed
        qed
      qed
      then obtain n where "QCongAAcute n" and "n B' PO N" 
        by blast
      have "Per B' N PO" 
        using \<open>A B' Perp PO N\<close> \<open>Col A B' N\<close> col_trivial_2 l8_16_1 l8_2 by blast
      moreover have "n N PO B'" 
        using \<open>QCongAACute n\<close> \<open>n B' PO N\<close> anga_sym by blast
      ultimately show ?thesis 
        by (metis \<open>ln PO N\<close> \<open>lb' PO B'\<close> Lcos_def \<open>QCong lb'\<close> \<open>QCong ln\<close> 
            \<open>\<exists>a. QCongAACute a \<and> a B' PO N\<close> anga_sym)
    qed
    then obtain n where "QCongAAcute n" and "Lcos ln lb' n" 
      by blast
    have "EqLcos lc l' lb' l" 
      using EqLcos_def \<open>Lcos ll' lb' l\<close> \<open>Lcos ll' lc l'\<close> by auto
    have "EqLcos lb l' lc' l" 
      using EqLcos_def \<open>Lcos ll lb l'\<close> \<open>Lcos ll lc' l\<close> by blast
    have "EqLcos lc m' la' m" 
      using EqLcos_def \<open>Lcos lm la' m\<close> \<open>Lcos lm lc m'\<close> by auto
    have "EqLcos la m' lc' m" 
      using EqLcos_def \<open>Lcos lm' la m'\<close> \<open>Lcos lm' lc' m\<close> by blast
    have "EqLcos la n' lb' n" 
      using EqLcos_def \<open>Lcos ln la n'\<close> \<open>Lcos ln lb' n\<close> by blast
    have "\<exists> lp. Lcos lp lb n'" 
    proof (rule lcos_exists, simp_all add: \<open>QCongAACute n'\<close> \<open>QCong lb\<close>)
      {
        assume "QCongNull lb" 
        then obtain X where "lb X X" 
          by (simp add: lg_null_instance)
        have "Cong B PO X X" 
          using \<open>QCong lb\<close> \<open>lb PO B\<close> \<open>lb X X\<close> lg_cong lg_sym by blast
        hence "B = PO" 
          by (simp add: cong_identity)
        hence False 
          by (simp add: assms(2))
      }
      thus "\<not> QCongNull lb" 
        by blast
    qed
    then obtain bn' where "Lcos bn' lb n'" 
      by blast
    have "\<not> QCongNull ll" 
      using \<open>Lcos ll lb l'\<close> lcos_not_lg_null by auto
    hence "\<exists> lp. Lcos lp ll n'" 
      using \<open>QCong ll\<close> \<open>QCongAACute n'\<close> lcos_exists by auto 
    then obtain bl'n' where "Lcos bl'n' ll n'" 
      by blast
    have "\<exists> lp. Lcos lp bn' l'"
    proof (rule lcos_exists, simp add: \<open>QCongAACute l'\<close>)
      show "QCong bn'" 
        using \<open>Lcos bn' lb n'\<close> lcos_lg_anga by blast
      show "\<not> QCongNull bn'" 
        using \<open>Lcos bn' lb n'\<close> lcos_lg_not_null by auto
    qed
    then obtain bn'l' where "Lcos bn'l' bn' l'"
      by blast
    have "Lcos2 bl'n' lb l' n'" 
      using Lcos2_def \<open>Lcos bl'n' ll n'\<close> \<open>Lcos ll lb l'\<close> by blast
    have "Lcos2 bn'l' lb n' l'" 
      using Lcos2_def \<open>Lcos bn' lb n'\<close> \<open>Lcos bn'l' bn' l'\<close> by blast
    have "bl'n' EqLTarski bn'l'" 
      using \<open>Lcos bl'n' ll n'\<close> \<open>Lcos bn' lb n'\<close> \<open>Lcos bn'l' bn' l'\<close> 
        \<open>Lcos ll lb l'\<close> l13_7 by blast
    have "EqLcos2 lb l' n' lb n' l'" 
      using EqLcos2_def \<open>Lcos2 bn'l' lb n' l'\<close> lcos2_comm by blast
    have "EqLcos2 lb l' n' lc' l n'" 
      by (simp add: \<open>EqLcos lb l' lc' l\<close> \<open>QCongAACute n'\<close> lcos_eq_lcos2_eq)
    have "EqLcos3 lb l' n' m lc' l n' m" 
      by (simp add: \<open>EqLcos lb l' lc' l\<close> \<open>QCongAACute m\<close> \<open>QCongAACute n'\<close> lcos_eq_lcos3_eq)
    have "EqLcos3 lb l' n' m lc' m l n'" 
    proof -
      obtain lp where "Lcos3 lp lb l' n' m" and "Lcos3 lp lc' l n' m" 
        using EqLcos3_def \<open>EqLcos3 lb l' n' m lc' l n' m\<close> by blast
      thus ?thesis
        by (meson EqLcos3_def lcos3_permut1 lcos3_permut3)
    qed
    have "EqLcos3 la m' l n' lc' m l n'" 
      using \<open>EqLcos la m' lc' m\<close> \<open>QCongAACute l\<close> \<open>QCongAACute n'\<close> lcos_eq_lcos3_eq by force
    hence "EqLcos3 lb l' n' m la m' l n'" 
      by (meson \<open>EqLcos3 lb l' n' m lc' m l n'\<close> 
          lcos3_eq_sym lcos3_eq_trans)
    hence "EqLcos3 lb l' n' m la n' m' l" 
      by (meson EqLcos3_def lcos3_permut1 lcos3_permut3)
    have "EqLcos3 la n' m' l lb' n m' l" 
      using \<open>EqLcos la n' lb' n\<close> \<open>QCongAACute l\<close> \<open>QCongAACute m'\<close> lcos_eq_lcos3_eq by blast
    hence "EqLcos3 lb l' n' m lb' n m' l" 
      using \<open>EqLcos3 lb l' n' m la n' m' l\<close> lcos3_eq_trans by blast
    hence "EqLcos3 lb l' n' m lb' l n m'" 
      by (meson EqLcos3_def lcos3_permut1 lcos3_permut3)
    have "EqLcos3 lb l' n' m lb' l n m'"
    proof -
      obtain lp where "Lcos3 lp lb l' n' m" and "Lcos3 lp lb' n m' l" 
        using EqLcos3_def \<open>EqLcos3 lb l' n' m lb' n m' l\<close> by auto
      thus ?thesis 
        using \<open>EqLcos3 lb l' n' m lb' l n m'\<close> by blast
    qed
    have "EqLcos3 lb' l n m' lc l' n m'" 
      by (simp add: \<open>EqLcos lc l' lb' l\<close> \<open>QCongAACute m'\<close> \<open>QCongAACute n\<close> 
          lcos_eq_lcos3_eq lcos_eq_sym)
    have "EqLcos3 lb l' n' m lc l' n m'" 
      using \<open>EqLcos3 lb l' n' m lb' l n m'\<close> \<open>EqLcos3 lb' l n m' lc l' n m'\<close> 
        lcos3_eq_trans by blast
    have "EqLcos3 lb l' n' m lc m' l' n" 
      by (meson EqLcos3_def \<open>EqLcos3 lb l' n' m lc l' n m'\<close> lcos3_permut1 lcos3_permut2)
    have "EqLcos3 la' m l' n lc m' l' n" 
      by (simp add: \<open>EqLcos lc m' la' m\<close> \<open>QCongAACute l'\<close> \<open>QCongAACute n\<close> 
          lcos_eq_lcos3_eq lcos_eq_sym)
    hence "EqLcos3 lb l' n' m la' m l' n" 
      by (meson \<open>EqLcos3 lb l' n' m lc m' l' n\<close> lcos3_eq_sym lcos3_eq_trans)
    hence "EqLcos3 lb l' n' m la' n l' m" 
      by (meson EqLcos3_def lcos3_permut2) 
    have "EqLcos2 lb l' n' la' n l'" 
      using \<open>EqLcos3 lb l' n' m la' n l' m\<close> lcos3_lcos2 by auto
    have "EqLcos2 lb n' l' la' n l'" 
      by (meson \<open>EqLcos2 lb l' n' la' n l'\<close> \<open>EqLcos2 lb l' n' lb n' l'\<close> lcos2_eq_sym lcos2_eq_trans)
    have "EqLcos lb n' la' n" 
      using \<open>EqLcos2 lb n' l' la' n l'\<close> lcos2_lcos by auto
    obtain ln' where "Lcos ln' lb n'" and "Lcos ln' la' n" 
      using EqLcos_def \<open>EqLcos lb n' la' n\<close> by blast
    have "PO \<noteq> N" 
      using \<open>Col A B' N\<close> \<open>\<not> Col A B' PO\<close> by auto
    have "Per A N PO"         
      using \<open>A B' Perp PO N\<close> \<open>Col A B' N\<close> col_trivial_3 l8_16_1 l8_2 by blast
    hence "n' A PO N" 
      using lcos_per_anga [where ?lp="la" and ?la="ln"] \<open>Lcos ln la n'\<close> 
        \<open>la PO A\<close> \<open>ln PO N\<close> lcos_per_anga by blast
    have "Per B' N PO" 
      using \<open>A B' Perp PO N\<close> \<open>Col A B' N\<close> col_trivial_2 l8_16_1 l8_2 by blast
    hence "n B' PO N" 
      using lcos_per_anga [where ?lp="lb'" and ?la="ln"] \<open>Lcos ln lb' n\<close> 
        \<open>lb' PO B'\<close> \<open>ln PO N\<close> lcos_per_anga by blast
    have "Bet A PO B \<or> PO Out A B \<or> \<not> Col A PO B" 
      using or_bet_out by presburger
    moreover 
    {
      assume "Bet A PO B"
      have "QCong ln'" 
        using \<open>Lcos ln' la' n\<close> lcos_lg_anga by blast
      then obtain N' where "ln' PO N'" and "Bet N PO N'" 
        using ex_point_lg_bet by blast
      {
        assume "PO = N'"
        hence "ln' PO PO" 
          using \<open>ln' PO N'\<close> by auto
        hence "QCongNull ln'"
          using \<open>QCong ln'\<close> by (simp add: lg_null_trivial)
        moreover have "\<not> QCongNull ln' \<and> \<not> QCongNull lb" 
          using lcos_lg_not_null \<open>Lcos ln' lb n'\<close> by force
        hence "\<not> QCongNull ln'" 
          by blast
        ultimately have False 
          by blast
      }
      hence "PO \<noteq> N'" 
        by blast
      {
        assume "A' = B"
        hence False 
          using assms(1) assms(4) by auto
      }
      hence "A' \<noteq> B" 
        by blast
      have "Per PO N' B"
      proof (rule lcos_per [where ?a = "n'" and ?l="lb" and ?lp="ln'"],
          simp_all add: \<open>QCongAACute n'\<close> \<open>QCong lb\<close> \<open>QCong ln'\<close> \<open>Lcos ln' lb n'\<close> 
          \<open>lb PO B\<close> \<open>ln' PO N'\<close>)
        have "N PO A CongA B PO N'" 
        proof (rule l11_13 [where ?A = "N'" and ?D = "A"], 
            simp_all add: \<open>Bet A PO B\<close> assms(2))
          show "N' PO A CongA A PO N'" 
            using \<open>A \<noteq> PO\<close> \<open>PO \<noteq> N'\<close> conga_pseudo_refl by force
          show "Bet N' PO N" 
            by (simp add: \<open>Bet N PO N'\<close> between_symmetry)
          show "N \<noteq> PO" 
            using \<open>PO \<noteq> N\<close> by blast
        qed
        thus "n' N' PO B" 
          using \<open>QCongAACute n'\<close> \<open>n' A PO N\<close> anga_conga_anga anga_sym by blast
      qed
      have "N PO B' CongA A' PO N'" 
      proof (rule l11_13 [where ?A = "N'" and ?D = "B'"])
        show "N' PO B' CongA B' PO N'" 
          using \<open>PO \<noteq> N'\<close> assms(6) conga_pseudo_refl by force
        show "Bet N' PO N" 
          using Bet_cases \<open>Bet N PO N'\<close> by auto
        show "N \<noteq> PO"  
          using \<open>PO \<noteq> N\<close> by blast
        have "Bet A' PO B'" 
          using l13_10_aux3 [where ?A="A" and ?B="B" and ?C="C"] \<open>Bet A PO B\<close> assms(1) 
            assms(10) assms(11) assms(2) assms(3) assms(4) assms(5) assms(6) 
            assms(7) assms(8) assms(9) by blast
        thus "Bet B' PO A'" 
          using between_symmetry by blast
        show "A' \<noteq> PO" 
          using assms(1) not_col_distincts by blast
      qed
      hence "n N' PO A'" 
        using \<open>QCongAACute n\<close> \<open>n B' PO N\<close> anga_conga_anga anga_sym by blast
      hence "Per PO N' A'"
        using lcos_per [where ?a="n" and ?l="ln'" and ?lp="la'"] 
          \<open>Lcos ln' la' n\<close> \<open>la' PO A'\<close> \<open>ln' PO N'\<close> lcos_lg_anga lcos_per by auto
      have ?thesis 
      proof (rule perp_col [where ?B="N'"])
        show "PO \<noteq> N" 
          by (simp add: \<open>PO \<noteq> N\<close>)
        show "PO N' Perp B A'"
        proof (rule cop_per2__perp)
          show "PO \<noteq> N'"                 
            by (simp add: \<open>PO \<noteq> N'\<close>)
          show "B \<noteq> A'"                 
            using \<open>A' \<noteq> B\<close> by auto
          show "N' \<noteq> B \<or> N' \<noteq> A'"                 
            using \<open>B \<noteq> A'\<close> by blast 
          have "Coplanar B N PO A'" 
          proof (rule col_cop__cop [where ?D="B'"])
            show "Coplanar B N PO B'" 
              using Coplanar_def \<open>Col A B' N\<close> assms(4) not_col_permutation_1 
                not_col_permutation_3 by blast
            show "PO \<noteq> B'" 
              using assms(6) by auto
            show "Col PO B' A'" 
              using Col_cases assms(8) by blast
          qed
          thus "Coplanar PO N' B A'"                 
            by (metis \<open>Bet N PO N'\<close> \<open>PO \<noteq> N\<close> bet_col bet_col1 col2_cop__cop 
                ncoplanar_perm_23 ncoplanar_perm_9)
          show "Per PO N' B"                 
            by (simp add: \<open>Per PO N' B\<close>)
          show "Per PO N' A'"             
            by (simp add: \<open>Per PO N' A'\<close>)
        qed
        show "Col PO N' N"     
          by (simp add: Col_def \<open>Bet N PO N'\<close>)
      qed
    }
    moreover 
    {
      assume "PO Out A B" 
      have "\<exists> N'. ln' PO N' \<and> PO Out N' N" 
      proof (rule ex_point_lg_out)
        show "PO \<noteq> N"             
          using \<open>PO \<noteq> N\<close> by blast
        show "QCong ln'"             
          using \<open>Lcos ln' la' n\<close> lcos_lg_anga by blast
        show "\<not> QCongNull ln'"
          using \<open>Lcos ln' la' n\<close> lcos_lg_not_null by blast
      qed
      then obtain N' where "ln' PO N'" and "PO Out N' N" 
        by blast
      have "Per PO N' B" 
      proof (rule lcos_per [where ?a="n'" and ?lp="ln'" and ?l="lb"],
          simp_all add: \<open>QCongAACute n'\<close> \<open>QCong lb\<close>  \<open>Lcos ln' lb n'\<close> 
          \<open>lb PO B\<close> \<open>ln' PO N'\<close>)
        show "QCong ln'" 
          using \<open>Lcos ln' la' n\<close> lcos_lg_anga by blast
        show "n' N' PO B" 
          using Out_cases \<open>PO Out A B\<close> \<open>PO Out N' N\<close> \<open>QCongAACute n'\<close> 
            \<open>n' A PO N\<close> anga_out_anga anga_sym by blast
      qed
      have "Per PO N' A'" 
      proof (rule lcos_per [where ?a="n" and ?lp="ln'" and ?l="la'"])
        show "QCongAACute n"  
          by (simp add: \<open>QCongAACute n\<close>)
        show "QCong la'"  
          using \<open>QCong la'\<close> by auto
        show "QCong ln'"  
          using \<open>Lcos ln' la' n\<close> lcos_lg_anga by blast
        show "Lcos ln' la' n"  
          by (simp add: \<open>Lcos ln' la' n\<close>)
        show "la' PO A'"  
          by (simp add: \<open>la' PO A'\<close>)
        show "ln' PO N'"  
          by (simp add: \<open>ln' PO N'\<close>)
        have "B' PO N CongA A' PO N'" 
        proof (rule out2__conga)
          show "PO Out A' B'" 
            using \<open>PO Out A B\<close> assms(1) assms(10) assms(11) assms(2) assms(3) 
              assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) l13_10_aux5 by blast
          show "PO Out N' N" 
            by (simp add: \<open>PO Out N' N\<close>)
        qed
        thus "n N' PO A'" 
          using \<open>QCongAACute n\<close> \<open>n B' PO N\<close> anga_conga_anga anga_sym by blast
      qed
      have ?thesis 
      proof (rule perp_col [where ?B = "N'"])
        show "PO \<noteq> N" 
          by (simp add: \<open>PO \<noteq> N\<close>)
        show "PO N' Perp B A'" 
        proof (rule cop_per2__perp)
          show "PO \<noteq> N'" 
            using \<open>PO Out N' N\<close> out_distinct by blast
          show "B \<noteq> A'" 
            using assms(1) assms(4) by fastforce
          show "N' \<noteq> B \<or> N' \<noteq> A'" 
            using \<open>B \<noteq> A'\<close> by force
          have "Coplanar B A' PO N'"
          proof (rule col_cop__cop [where ?D = "N"])
            have "Coplanar B N PO A'"
            proof (rule col_cop__cop [where ?D = "B'"])
              show "Coplanar B N PO B'"     
                using Col_cases Coplanar_def \<open>Col A B' N\<close> assms(4) by auto
              show "PO \<noteq> B'"     
                using assms(6) by auto
              show "Col PO B' A'"
                using assms(8) not_col_permutation_5 by blast
            qed
            thus "Coplanar B A' PO N" 
              using coplanar_perm_5 by blast
            show "PO \<noteq> N" 
              by (simp add: \<open>PO \<noteq> N\<close>)
            show "Col PO N N'" 
              using Out_cases \<open>PO Out N' N\<close> out_col by blast
          qed
          thus  "Coplanar PO N' B A'" 
            using coplanar_perm_16 by blast
          show "Per PO N' B" 
            using \<open>Per PO N' B\<close> by blast
          show "Per PO N' A'" 
            using \<open>Per PO N' A'\<close> by blast
        qed
        show "Col PO N' N" 
          by (simp add: \<open>PO Out N' N\<close> out_col)
      qed
    }
    moreover have "\<not> Col A PO B \<longrightarrow> ?thesis" 
      using assms(4) not_col_permutation_4 by blast
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis 
    using Perp2_def by blast

qed

end

subsubsection "Pappus' theorem in euclidean "

context Tarski_Euclidean

begin

lemma cop_par__perp2: 
  assumes "Coplanar A B C P" and
    "A B Par C D"
  shows "P Perp2 A B C D" 
proof -
  obtain Q where "A B Perp Q P" and "Coplanar A B C Q" 
    using assms(2) ex_perp_cop par_neq1 by blast
  have "Col P P Q" 
    by (simp add: col_trivial_1)
  moreover have "P Q Perp A B" 
    using Perp_perm \<open>A B Perp Q P\<close> by blast
  moreover 
  have "C D Perp P Q" 
  proof (rule cop_par_perp__perp [where ?A = "A" and ?B = "B"])
    show "A B Par C D" 
      by (simp add: assms(2))
    show "A B Perp P Q"  
      by (simp add: \<open>A B Perp Q P\<close> perp_right_comm)
    {
      assume "C D ParStrict A B"
      have "Coplanar C D P Q" 
      proof (rule coplanar_pseudo_trans [where ?P = "A" and ?Q = "B" and ?R = "C"])
        show "\<not> Col A B C" 
          using \<open>C D ParStrict A B\<close> par_strict_not_col_3 by blast
        show "Coplanar A B C C" 
          using ncop_distincts by blast
        show "Coplanar A B C D" 
          using assms(2) par_cong_cop by blast
        show "Coplanar A B C P" 
          by (simp add: assms(1))
        show "Coplanar A B C Q" 
          by (simp add: \<open>Coplanar A B C Q\<close>)
      qed
    }
    moreover 
    {
      assume "C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B"
      have "Coplanar P Q C D" 
      proof (rule col2_cop__cop [where ?C = "A" and ?D = "B"])
        show "Coplanar P Q A B" 
          using \<open>P Q Perp A B\<close> perp__coplanar by blast
        show "A \<noteq> B" 
          using \<open>C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B\<close> by force
        show "Col A B C" 
          using Col_cases \<open>C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B\<close> by blast
        show "Col A B D" 
          using Col_cases \<open>C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B\<close> by blast
      qed
      hence "Coplanar C D P Q" 
        using coplanar_perm_16 by blast
    }
    ultimately show "Coplanar C D P Q"  
      using Par_cases Par_def assms(2) by blast
  qed
  hence "P Q Perp C D" 
    using Perp_cases by blast
  ultimately show ?thesis 
    using Perp2_def by blast
qed


lemma l13_11:
  assumes "\<not> Col PO A A'" and
    "B \<noteq> PO" and 
    "C \<noteq> PO" and
    "Col PO A B" and
    "Col PO B C" and
    "B' \<noteq> PO" and 
    "C' \<noteq> PO" and
    "Col PO A' B'" and
    "Col PO B' C'" and
    "B C' Par C B'" and
    "C A' Par A C'"
  shows "A B' Par B A'" 
proof -
  have "Coplanar B C' C PO" 
    using Col_cases assms(5) ncop__ncols by blast
  have "Coplanar C A' PO A" 
  proof (rule col_cop__cop [where ?D = "B"])
    show "Coplanar C A' PO B" 
      using Col_cases assms(5) ncop__ncols by blast
    show "PO \<noteq> B" 
      using assms(2) by blast
    show "Col PO B A" 
      using Col_cases assms(4) by blast
  qed
  hence "Coplanar C A' A PO" 
    using coplanar_perm_1 by blast
  have "PO Perp2 B C' C B'" 
    by (simp add: \<open>Coplanar B C' C PO\<close> assms(10) cop_par__perp2)
  have "PO Perp2 C A' A C'"
    by (simp add: \<open>Coplanar C A' A PO\<close> assms(11) cop_par__perp2)
  have "PO Perp2 A B' B A'" 
    using \<open>PO Perp2 B C' C B'\<close> \<open>PO Perp2 C A' A C'\<close> assms(1) assms(2) assms(3) 
      assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) l13_10 by blast
  then obtain X Y where "Col PO X Y" and "X Y Perp A B'" and "X Y Perp B A'" 
    using Perp2_def by blast
  have "Coplanar A X PO A'" 
  proof (rule col_cop__cop [where ?D="B'"])
    have "Coplanar A B' X PO"
    proof (rule col_cop__cop [where ?D = "Y"])
      show "Coplanar A B' X Y" 
        using \<open>X Y Perp A B'\<close> coplanar_perm_16 perp__coplanar by blast
      show "X \<noteq> Y" 
        using \<open>X Y Perp B A'\<close> perp_distinct by blast
      show "Col X Y PO" 
        using Col_cases \<open>Col PO X Y\<close> by blast
    qed
    thus "Coplanar A X PO B'" 
      using coplanar_perm_3 by blast
    show "PO \<noteq> B'" 
      using assms(6) by blast
    show "Col PO B' A'" 
      using assms(8) not_col_permutation_5 by blast
  qed
  hence "Coplanar PO A A' X" 
    using coplanar_perm_13 by blast
  have "Coplanar A Y PO A'" 
  proof (rule col_cop__cop [where ?D = "B'"])
    have "Coplanar A B' Y PO" 
    proof (rule col_cop__cop [where ?D = "X"])
      show "Coplanar A B' Y X" 
        using \<open>X Y Perp A B'\<close> coplanar_perm_17 perp__coplanar by blast
      show "Y \<noteq> X" 
        using \<open>X Y Perp A B'\<close> perp_not_eq_1 by blast
      show "Col Y X PO" 
        using \<open>Col PO X Y\<close> not_col_permutation_3 by blast
    qed
    thus "Coplanar A Y PO B'" 
      using coplanar_perm_3 by blast
    show "PO \<noteq> B'" 
      using assms(6) by blast
    show "Col PO B' A'" 
      using assms(8) not_col_permutation_5 by blast
  qed
  hence "Coplanar PO A A' Y" 
    using coplanar_perm_13 by blast
  show ?thesis
  proof (rule l12_9 [where ?C1.0="X" and ?C2.0="Y"])
    show "Coplanar X Y A B" 
      using Coplanar_def \<open>Col PO X Y\<close> assms(4) col_permutation_1 by blast
    show "Coplanar X Y A A'"
      by (meson \<open>Coplanar PO A A' X\<close> \<open>Coplanar PO A A' Y\<close> assms(1) 
          coplanar_pseudo_trans ncop_distincts)
    show "Coplanar X Y B' B"
    proof (rule coplanar_pseudo_trans [where ?P = "PO" and ?Q = "A" and ?R = "A'"],
        simp_all add: assms(1) \<open>Coplanar PO A A' X\<close> \<open>Coplanar PO A A' Y\<close>)
      show "Coplanar PO A A' B'" 
        using assms(8) ncop__ncols by auto
      show "Coplanar PO A A' B" 
        using assms(4) ncop__ncols by blast
    qed
    show "Coplanar X Y B' A'" 
    proof (rule coplanar_pseudo_trans [where ?P = "PO" and ?Q ="A" and ?R = "A'"],
        simp_all add: assms(1)\<open>Coplanar PO A A' X\<close>\<open>Coplanar PO A A' Y\<close>)
      show "Coplanar PO A A' B'" 
        using assms(8) ncop__ncols by blast
      show "Coplanar PO A A' A'"
        using ncop_distincts by blast
    qed
    show "A B' Perp X Y" 
      using Perp_perm \<open>X Y Perp A B'\<close> by blast
    show "B A' Perp X Y" 
      using Perp_perm \<open>X Y Perp B A'\<close> by blast
  qed
qed

lemma l13_14:
  assumes "PO A ParStrict O' A'" and
    "Col PO A B" and
    "Col PO B C" and
    "Col PO A C" and
    "Col O' A' B'" and
    "Col O' B' C'" and
    "Col O' A' C'" and
    "A C' Par A' C" and
    "B C' Par B' C" 
  shows "A B' Par A' B" 
proof -
  have "PO \<noteq> A" 
    using assms(1) par_strict_distinct by blast
  have "O' \<noteq> A'" 
    using assms(1) par_strict_neq2 by auto
  have "\<not> Col PO A A'" 
    using assms(1) par_strict_not_col_4 by presburger
  {
    assume "A = C"
    have "A C' ParStrict A' A \<longrightarrow> ?thesis" 
      using Par_strict_cases not_par_strict_id by blast
    hence ?thesis 
      by (metis Par_def Par_perm Par_strict_perm \<open>A = C\<close> assms(1) assms(7) 
          assms(8) assms(9) col_trivial_2 colx par_strict_not_col_3)
  }
  moreover 
  {
    assume "A \<noteq> C"
    hence "A' \<noteq> C'" 
      using Par_cases \<open>\<not> Col PO A A'\<close> assms(4) assms(8) col2__eq par_id by blast
    have "A C ParStrict A' C'" 
      by (meson \<open>A \<noteq> C\<close> \<open>A' \<noteq> C'\<close> assms(1) assms(4) assms(7) col_trivial_2 
          par_strict_col4__par_strict)
    have "Plg A C A' C'" 
      by (metis Col_cases Par_cases \<open>A C ParStrict A' C'\<close> assms(8) l12_19 
          not_cong_4321 par_id_5 par_par_cong_cong_parallelogram par_strict_not_col_3 
          par_strict_par parallelogram_to_plg)
    {
      assume "B = C"
      hence "A C' Par A' B" 
        using assms(8) by force
      have "B' = C'" 
      proof -
        have "\<not> Col B C' A'" 
          using \<open>A C ParStrict A' C'\<close> \<open>B = C\<close> col_permutation_5 par_strict_not_col_2 by blast
        moreover have "A' \<noteq> C'" 
          by (simp add: \<open>A' \<noteq> C'\<close>)
        moreover have "Col B C' B'" 
          using \<open>B = C\<close> assms(9) par_id par_right_comm by blast
        moreover have "Col B C' C'" 
          by (meson not_col_distincts)
        moreover have "Col A' C' B'" 
          using \<open>O' \<noteq> A'\<close> assms(5) assms(7) col_transitivity_2 by blast
        moreover have "Col A' C' C'" 
          by (simp add: col_trivial_2)
        ultimately show ?thesis 
          using l6_21 by blast
      qed
      hence "A B' Par A' B"  
        using \<open>A C' Par A' B\<close> by blast
      hence ?thesis 
        by simp
    }
    moreover 
    {
      assume "B \<noteq> C"
      {
        assume "B' = C'" 
        have "B B' ParStrict B' C \<longrightarrow> False" 
          using Par_strict_cases not_par_strict_id by blast
        moreover 
        {
          assume "B \<noteq> B'" and "B' \<noteq> C" and "Col B B' C" and "Col B' B' C"
          have "B = C" 
          proof -
            have "\<not> Col A C B'" 
              using \<open>A C ParStrict A' C'\<close> \<open>B' = C'\<close> par_strict_not_col_4 by auto
            moreover have "B' \<noteq> B" 
              using \<open>B \<noteq> B'\<close> by blast
            moreover have "Col A C B" 
              using \<open>PO \<noteq> A\<close> assms(2) assms(4) col_transitivity_2 by blast
            moreover have "Col A C C" 
              using not_col_distincts by blast
            moreover have "Col B' B B" 
              using not_col_distincts by auto
            moreover have "Col B' B C" 
              using \<open>Col B B' C\<close> not_col_permutation_4 by blast
            ultimately show ?thesis 
              using l6_21 by blast
          qed
          hence False 
            by (simp add: \<open>B \<noteq> C\<close>)
        }
        ultimately have False 
          using Par_def \<open>B' = C'\<close> assms(9) by force
      }
      hence "B' \<noteq> C'" 
        by blast
      hence "B C ParStrict B' C'" 
        using \<open>B \<noteq> C\<close> assms(1) assms(2) assms(4) assms(5) assms(7) 
          par_strict_col4__par_strict by blast
      have "Plg B C B' C'"
        using pars_par_plg \<open>B C ParStrict B' C'\<close> assms(9) par_right_comm by blast
      have "Parallelogram A C A' C'" 
        by (simp add: \<open>Plg A C A' C'\<close> parallelogram_equiv_plg)
      have "Parallelogram B C B' C'" 
        by (simp add: \<open>Plg B C B' C'\<close> parallelogram_equiv_plg)
      obtain M where "M Midpoint A A'" and "M Midpoint C C'" 
        using Plg_def \<open>Plg A C A' C'\<close> by blast
      obtain N where "N Midpoint B B'" and "N Midpoint C C'" 
        using Plg_def \<open>Plg B C B' C'\<close> by blast
      hence "M = N" 
        using \<open>M Midpoint C C'\<close> l7_17 by auto
      have "Parallelogram A B A' B'" 
        using mid_plg by (metis \<open>A C ParStrict A' C'\<close> \<open>M = N\<close> \<open>M Midpoint A A'\<close> 
            \<open>N Midpoint B B'\<close> not_par_strict_id)
      have "A B' Par B A'"
      proof (cases "A = B")
        case True
        hence "A' = B'" 
          using symmetric_point_uniqueness \<open>M = N\<close> \<open>M Midpoint A A'\<close> 
            \<open>N Midpoint B B'\<close> by blast
        thus ?thesis 
          by (metis True \<open>\<not> Col PO A A'\<close> assms(2) par_reflexivity)
      next
        case False
        hence "B \<noteq> A'" 
          using \<open>\<not> Col PO A A'\<close> assms(2) by auto
        thus ?thesis using plg_par 
          by (simp add: False \<open>Parallelogram A B A' B'\<close>)
      qed
      hence ?thesis 
        using par_right_comm by presburger
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed  

end
end
