(* IsageoCoq2_R1

Gupta.thy

Version 2.2.0 IsaGeoCoq2_R1, Port part of GeoCoq 3.4.0

Copyright (C) 2022-2023 Roland Coghetto roland.coghetto ( a t ) cafr-msa2p.be
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
theory Gupta

imports
  Tarski_Neutral
  Tarski_2D

begin
  (*>*)

section "Gupta inspired variant of Tarski - Geometry"

subsection "Axioms - neutral dimension less"

locale Gupta_neutral_dimensionless =
  fixes GPA GPB GPC :: TPoint 
  and BetG  :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  and CongG :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"

assumes cong_pseudo_reflexivityG: "\<forall> a b. 

CongG a b b a"

and   cong_inner_transitivityG: "\<forall> a b p q r s.

CongG a b p q \<and>
CongG a b r s
\<longrightarrow>
CongG p q r s"

and   cong_identityG: "\<forall> a b c.

CongG a b c c
\<longrightarrow>
a = b"

and   segment_constructionG: "\<forall> a b c q.

\<exists>x. (BetG q a x \<and> CongG a x b c)"

and   five_segmentG: "\<forall> a b c d a' b' c' d'.

a \<noteq> b \<and>
BetG a b c \<and>
BetG a' b' c'\<and>
CongG a b a' b' \<and>
CongG b c b' c' \<and>
CongG a d a' d' \<and>
CongG b d b' d'
\<longrightarrow>
CongG c d c' d'"

(*and   between_identity: "\<forall> a b.

Bet a b a
\<longrightarrow>
a = b"*)
and   between_symmetryG: "\<forall> a b c.

BetG a b c
\<longrightarrow>
BetG c b a"

and   between_inner_transitivityG: "\<forall> a b c d.

BetG a b d \<and>
BetG b c d
\<longrightarrow>
BetG a b c"

and   inner_paschG: "\<forall> a b c p q.

BetG a p c \<and>
BetG b q c \<and>
a \<noteq> p \<and>
c \<noteq> p \<and>
b \<noteq> q \<and>
c \<noteq> q \<and>
\<not> (BetG a b c \<or> BetG b c a \<or> BetG c a b)
\<longrightarrow> 
(\<exists> x. BetG p x b \<and> BetG q x a)"

and   lower_dimG:  "\<not> (BetG GPA GPB GPC \<or> BetG GPB GPC GPA \<or> BetG GPC GPA GPB)"

subsection "Definitions"

definition (in Gupta_neutral_dimensionless) ColG :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "ColG A B C \<equiv> BetG A B C \<or> BetG B C A \<or> BetG C A B"

subsection "Axioms: neutral 2D"

locale Gupta_neutral_2D = Gupta_neutral_dimensionless GPA GPB GPC BetG CongG
  for GPA GPB GPC :: TPoint 
  and BetG  :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  and CongG :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool" +
  assumes upper_dimG: "\<forall> a b c p q.
                      p \<noteq> q \<and>
a \<noteq> b \<and>
a \<noteq> c \<and>
c \<noteq> b \<and>
                      CongG a p a q \<and>
                      CongG b p b q \<and>
                      CongG c p c q
                      \<longrightarrow>
                      (BetG a b c \<or> BetG b c a \<or> BetG c a b)"


subsection "Axioms: euclidean"

locale Gupta_euclidean = Gupta_neutral_dimensionless GPA GPB GPC BetG CongG
  for GPA GPB GPC :: TPoint 
  and BetG  :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  and CongG :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool" +
  assumes euclidG: "\<forall> A B C D T.
   BetG A D T \<and> BetG B D C \<and> B \<noteq> D \<and> D \<noteq> C \<and>
   \<not> (BetG A B C \<or> BetG B C A \<or> BetG C A B) \<longrightarrow>
(\<exists> x y. BetG A B x \<and> BetG A C y \<and> BetG x T y)"

context Gupta_neutral_dimensionless

begin

lemma g2_1: 
  shows "CongG A B A B" 
  using cong_inner_transitivityG cong_pseudo_reflexivityG by blast

lemma g2_2:
  assumes "CongG A B C D"
  shows "CongG C D A B" 
  using assms cong_inner_transitivityG g2_1 by blast

lemma cong_inner_transitivityT:
  assumes "CongG A B C D" and
    "CongG A B E F"
  shows "CongG C D E F" 
  using assms(1) assms(2) cong_inner_transitivityG by blast

lemma g2_3:
  assumes "CongG A B C D" 
  shows "CongG B A C D" 
  using cong_inner_transitivityT assms cong_pseudo_reflexivityG by blast

lemma g2_4:
  assumes "CongG A B C D"
  shows "CongG A B D C" 
  using assms g2_2 g2_3 by presburger

lemma g2_5_a:
  assumes "CongG A B C D" and
    "A = B"
  shows "C = D" 
  using cong_identityG assms(1) assms(2) g2_2 by blast

lemma g2_5_b:
  assumes "CongG A B C D" and
    "C = D"
  shows "A = B" 
  using assms(1) assms(2) cong_identityG by blast

lemma g2_5:
  assumes "CongG A B C D"
  shows "A = B \<longleftrightarrow> C = D" 
  using Gupta_neutral_dimensionless.g2_5_a Gupta_neutral_dimensionless_axioms assms 
    cong_identityG by blast

lemma g2_6:
  shows "BetG A B B \<and> CongG B B A A" 
  using cong_identityG segment_constructionG by blast

lemma g2_7:
  assumes "CongG A B A' B'" and 
    "CongG B C B' C'" and
    "BetG A B C" and
    "BetG A' B' C'"
  shows "CongG A C A' C'"
proof (cases "A = B")
  case True
  thus ?thesis
    using assms(1) assms(2) g2_5_a by blast
next
  case False
  have "BetG A' A A" 
    by (simp add: g2_6)
  moreover have "CongG A A A' A'" 
    using g2_6 by auto
  ultimately have "CongG B A B' A'" 
    using assms(1) g2_3 g2_4 by blast
  thus ?thesis 
    by (meson False \<open>CongG A A A' A'\<close> assms(2) assms(3) assms(4) five_segmentG g2_3 g2_4)
qed

lemma g2_8:
  assumes "BetG A B C" and
    "BetG A B D" and
    "CongG B C B D" and
    "A \<noteq> B" 
  shows "C = D" 
  by (meson assms(1) assms(2) assms(3) assms(4) five_segmentG g2_1 g2_5_b)

lemma g2_9:
  assumes "BetG A B A"
  shows "BetG C A B" 
  using assms between_inner_transitivityG g2_6 by blast

lemma g2_10:
  assumes "BetG A B A"
  shows "BetG C B A" 
  by (simp add: assms g2_9)

lemma g2_11:
  assumes "BetG A B A" and
    "A \<noteq> B"
  shows "\<exists> D. BetG C D C \<and> BetG D C D \<and> C \<noteq> D" 
  by (metis(full_types) assms(1) assms(2) between_symmetryG g2_8 g2_9 segment_constructionG)

lemma g2_12:
  assumes "BetG A B A" 
  shows "BetG A B C" 
  using assms between_symmetryG g2_10 by blast

lemma g2_13:
  assumes "BetG A B A" and
    "A \<noteq> B"
  shows "BetG C B C" 
  by (metis assms(1) assms(2) between_symmetryG g2_10 g2_8 segment_constructionG)

lemma g2_14_1: 
  assumes "BetG A B A" and
    "A \<noteq> B" 
  shows "BetG C D C" 
  by (metis assms(1) assms(2) g2_13 g2_9)

lemma g2_14_2: 
  assumes "BetG A B A" and
    "A \<noteq> B" 
  shows "BetG D C D" 
  using assms(1) assms(2) g2_14_1 by blast

lemma g2_14: 
  assumes "BetG A B A" and
    "A \<noteq> B" 
  shows "BetG C D C \<and> BetG D C D"
  using assms(1) assms(2) g2_14_2 by blast

lemma g2_15:
  assumes "BetG A B A" and
    "A \<noteq> B"
  shows "BetG C D E" 
  using assms(1) assms(2) g2_14 g2_9 by blast

lemma g2_16:
  assumes "\<not> BetG C D E" and
    "BetG A B A"
  shows "A = B" 
  by (meson assms(1) assms(2) g2_15)

lemma between_identityT:
  assumes "BetG A B A"
  shows "A = B" 
  using lower_dimG assms g2_16 by blast

lemma cong_trivial_identityT:
  shows "CongG A A B B" 
  by (simp add: g2_6)

lemma l2_11T:
  assumes "BetG A B C" and
    "BetG A' B' C'" and
    "CongG A B A' B'" and
    "CongG B C B' C'"
  shows "CongG A C A' C'" 
  using assms(1) assms(2) assms(3) assms(4) g2_7 by blast

lemma construction_uniquenessT:
  assumes "Q \<noteq> A" and
    "BetG Q A X" and
    "CongG A X B C" and
    "BetG Q A Y" and
    "CongG A Y B C"
  shows "X = Y" 
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) cong_inner_transitivityG g2_2 g2_8)

lemma between_trivialT: 
  shows "BetG A B B" 
  using g2_6 by auto

lemma bet_decG:
  shows "BetG A B C \<or> \<not> BetG A B C" 
  by simp

lemma col_decG:
  shows "ColG A B C \<or> \<not> ColG A B C" 
  by simp

lemma inner_paschT:
  assumes "BetG A P C" and 
    "BetG B Q C" 
  shows "\<exists> x. BetG P x B \<and> BetG Q x A" 
proof -
  {
    assume "A \<noteq> P"
    {
      assume "P \<noteq> C"
      {
        assume "B \<noteq> Q"
        {
          assume "Q \<noteq> C"
          have "ColG A B C \<longrightarrow> ?thesis" 
          proof -
            have "BetG A B C \<longrightarrow> ?thesis" 
              using assms(2) between_inner_transitivityG between_symmetryG 
                between_trivialT by blast
            moreover have "BetG B C A \<longrightarrow> ?thesis" 
              using assms(1) assms(2) between_inner_transitivityG between_symmetryG by blast
            moreover have "BetG C A B \<longrightarrow> ?thesis" 
              by (meson assms(1) between_inner_transitivityG between_symmetryG 
                  between_trivialT)
            ultimately show ?thesis 
              using ColG_def by presburger
          qed
          moreover have "\<not> ColG A B C \<longrightarrow> ?thesis" 
            using ColG_def \<open>A \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>P \<noteq> C\<close> \<open>Q \<noteq> C\<close> assms(1) assms(2) 
              inner_paschG by blast
          ultimately have ?thesis 
            by blast
        }
        hence ?thesis 
          using assms(1) between_symmetryG between_trivialT by blast
      }
      hence ?thesis 
        using between_symmetryG g2_6 by blast
    }
    hence ?thesis 
      using assms(2) between_symmetryG g2_6 by blast
  }
  thus ?thesis
    using between_symmetryG g2_6 by blast
qed

end

context Gupta_neutral_2D

begin

lemma upper_dimT :
  assumes "P \<noteq> Q" and
    "CongG A P A Q" and
    "CongG B P B Q" and
    "CongG C P C Q" 
  shows "BetG A B C \<or> BetG B C A \<or> BetG C A B" 
  by (metis Gupta_neutral_2D.upper_dimG Gupta_neutral_2D_axioms assms(1) assms(2) 
      assms(3) assms(4) between_trivialT)

end

end
