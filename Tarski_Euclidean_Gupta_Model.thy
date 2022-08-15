(* IsageoCoq2_R1

Tarski_Euclidean_Gupta_Model.thy

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
theory Tarski_Euclidean_Gupta_Model

imports 
  Gupta
  Tarski_Gupta_Model
  Tarski_Euclidean
  Gupta_Euclidean_Tarski_Model

begin
  (*>*)

context Gupta_euclidean

begin

lemma euclidT:
  assumes "BetG A D T" and
    "BetG B D C" and 
    "A \<noteq> D" and
    "\<forall> A B C D T.
     BetG A D T \<and> BetG B D C \<and> A \<noteq> D 
\<longrightarrow>
     (\<exists> X Y. BetG A B X \<and> BetG A C Y \<and> BetG X T Y)"
  shows "\<exists> X Y. BetG A B X \<and> BetG A C Y \<and> BetG X T Y" 
proof -
  {
    assume "B \<noteq> D"
    {
      assume "ColG A B C" 
      {
        assume "BetG A B C"
        {
          assume "A \<noteq> B"
          moreover have "BetG A B C" 
            using \<open>BetG A B C\<close> by blast
          moreover have "BetG A B T" 
            using assms(1) assms(2) g_between_exchange4 
              g_between_inner_transitivity calculation(2) by blast
          moreover have "BetG B C T \<longrightarrow> ?thesis" 
            using calculation(3) g_not_bet_distincts by blast
          moreover have "BetG B T C \<longrightarrow> ?thesis" 
            using g_not_bet_distincts by blast
          ultimately have ?thesis using g_l5_2 by blast
        }
        hence ?thesis 
          using g_between_symmetry g_between_trivial by blast
      }
      moreover have "BetG B C A \<longrightarrow> ?thesis" 
        using assms(1) assms(2) assms(3) assms(4) by presburger
      moreover have "BetG C A B \<longrightarrow> ?thesis" 
        using assms(1) assms(2) assms(3) assms(4) by presburger
      ultimately have ?thesis 
        using ColG_def \<open>ColG A B C\<close> by blast
    }
    moreover
    {
      assume "\<not> ColG A B C" 
      {
        {
          assume "D \<noteq> C"
          hence ?thesis 
            using assms(1) assms(2) assms(3) assms(4) by blast
        }
        hence ?thesis 
          using assms(1) g_not_bet_distincts by blast
      }
      hence ?thesis 
        by blast
    }
    ultimately have ?thesis 
      by blast
  }
  thus ?thesis 
    using assms(1) g_between_symmetry g_between_trivial by blast
qed

lemma lem_euclidG: 
  assumes "BetG A D T" and
    "BetG B D C" and 
    "A \<noteq> D" 
  shows "\<exists> X Y. BetG A B X \<and> BetG A C Y \<and> BetG X T Y" 
proof -
  {
    assume "B \<noteq> D" and "D \<noteq> C" and
      "\<not> (BetG A B C \<or> BetG B C A \<or> BetG C A B)"
    hence ?thesis 
      using assms(1) assms(2) euclidG by presburger
  }
  moreover
  {
    assume "B = D"
    hence ?thesis 
      using assms(1) g_not_bet_distincts by blast
  }
  moreover
  {
    assume "D = C"
    hence ?thesis 
      using assms(1) g_between_trivial by blast
  }
  moreover
  {
    assume "BetG A B C \<or> BetG B C A \<or> BetG C A B"
    moreover have "BetG A B C \<longrightarrow> ?thesis" 
      by (meson assms(1) assms(2) between_inner_transitivityG g_between_exchange4 
          g_not_bet_distincts)
    moreover have "BetG B C A \<longrightarrow> ?thesis" 
      by (metis assms(1) assms(2) between_inner_transitivityG between_symmetryG 
          g_between_exchange4 g_not_bet_distincts segment_constructionG)    
    moreover 
    {
      assume "BetG C A B"
      hence "BetG B A D \<or> BetG B D A" 
        using assms(1) assms(2) g_l5_3 g_between_symmetry by blast
      moreover
      {
        assume "BetG B A D"
        hence "\<exists> X Y. BetG A B X \<and> BetG A C Y \<and> BetG X T Y" 
          using assms(1) assms(2) assms(3) between_symmetryG g_between_exchange4 g_l5_2 
            g_not_bet_distincts by metis
      }
      moreover
      {
        assume "BetG B D A"
        hence "\<exists> X Y. BetG A B X \<and> BetG A C Y \<and> BetG X T Y" 
          using assms(1) assms(2) assms(3) between_symmetryG g_between_exchange4 g_l5_2 
            g_not_bet_distincts by metis
      }
      ultimately have "\<exists> X Y. BetG A B X \<and> BetG A C Y \<and> BetG X T Y" 
        by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

interpretation Interpretation_Tarski_euclidean : Tarski_Euclidean 
  where Bet = BetG and Cong = CongG and
    TPA = GPA and TPB = GPB and TPC = GPC
proof
  show "\<forall>a b. CongG a b b a" 
    by (simp add: cong_pseudo_reflexivityG)
  show "\<forall>a b p q r s. CongG a b p q \<and> CongG a b r s \<longrightarrow> CongG p q r s" 
    using cong_inner_transitivityG by blast
  show "\<forall>a b c. CongG a b c c \<longrightarrow> a = b" 
    by (simp add: cong_identityG)
  show "\<forall>a b c q. \<exists>x. BetG q a x \<and> CongG a x b c" 
    by (simp add: segment_constructionG)
  show "\<forall>a b c d a' b' c' d'. a \<noteq> b \<and> BetG a b c \<and> BetG a' b' c' \<and> 
            CongG a b a' b' \<and> CongG b c b' c' \<and> CongG a d a' d' \<and> CongG b d b' d' \<longrightarrow>
       CongG c d c' d'" 
    using five_segmentG by blast
  show "\<forall>a b. BetG a b a \<longrightarrow> a = b" 
    by (simp add: between_identityT)
  show "\<forall>a b c p q. BetG a p c \<and> BetG b q c \<longrightarrow> (\<exists>x. BetG p x b \<and> BetG q x a)" 
    using inner_paschT by blast
  show "\<not> BetG GPA GPB GPC \<and> \<not> BetG GPB GPC GPA \<and> \<not> BetG GPC GPA GPB" 
    using lower_dimG by blast
  show "\<forall>A B C D T.
       BetG A D T \<and> BetG B D C \<and> A \<noteq> D \<longrightarrow>
       (\<exists>X Y. BetG A B X \<and> BetG A C Y \<and> BetG X T Y)" 
    using lem_euclidG by blast
qed

end
end
