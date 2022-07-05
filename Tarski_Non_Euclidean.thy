(* IsageoCoq2_R1

Tarski_Non_Euclidean.thy

Version 2.1.0 IsaGeoCoq2_R1
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

section "In Tarski Non Euclidean"

(* TODO
NPost04 ?
NPost31 ?
NPost32 ?
NPost33 ?
NPost34 ?
*)
theory Tarski_Non_Euclidean

imports
  Tarski_Neutral
  Tarski_Postulate_Parallels

begin


subsection "Definitions"

locale Tarski_Non_Euclidean = Tarski_neutral_dimensionless +
  fixes A0 B0 C0 D0 T0
  assumes NERule1: "Bet A0 D0 T0" and
    NERule2: "Bet B0 D0 C0" and
    NERule3: "A0 \<noteq> D0" and
    not_tarski_s_parallel_postulate_aux: 
    "\<forall> X Y. ((Bet A0 B0 X \<and> Bet A0 C0 Y) \<longrightarrow> \<not> Bet X T0 Y)" 

lemma (in Tarski_Non_Euclidean) Tarski_Pre_Non_Euclidean_aux:
  shows "\<exists> A B C D T. \<not> ((Bet A D T \<and> Bet B D C \<and> A \<noteq> D) 
                         \<longrightarrow>
                      (\<exists> X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y))" 
  using NERule1 NERule2 NERule3 not_tarski_s_parallel_postulate_aux by blast

locale Tarski_Greenberg_Non_Euclidean = Tarski_Non_Euclidean +
  assumes greenberg: "\<forall> P Q R A B C. 
\<not> Col A B C \<and> Acute A B C \<and> Q \<noteq> R \<and> Per P Q R \<longrightarrow>
(\<exists> S. P S Q LtA A B C \<and> Q Out S R)"

subsection "Theorems - Postulates"

subsection "Tarski non euclidean (General)"

context Tarski_Non_Euclidean

begin



lemma NPost01:
  shows "\<not> Postulate01" 
  using Postulate01_def Tarski_Pre_Non_Euclidean_aux 
    tarski_s_parallel_postulate_def by blast

theorem not_tarski_s_parallel_postulate_thm:
  shows "\<exists> A B C D T. (Bet A D T \<and> Bet B D C \<and> A \<noteq> D \<and> 
                      (\<forall> X Y. (Bet A B X \<and> Bet A C Y) \<longrightarrow> \<not> Bet X T Y))" 
  using Tarski_Pre_Non_Euclidean_aux by blast

lemma NPost02:
  shows "\<not> Postulate02" 
  using InterAx5 NPost01 by blast

theorem not_playfair_s_postulate_thm:
  shows "\<exists> A1 A2 B1 B2 C1 C2 P. A1 A2 Par B1 B2 \<and> 
Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 \<and>
    ( \<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2)" 
  using NPost02 Postulate02_def playfair_s_postulate_def by blast

lemma NPost05:
  shows "\<not> Postulate05" 
  using NPost02 Postulate02_def Postulate05_def par_trans_implies_playfair by blast

theorem not_postulate_of_transitivity_of_parallelism_thm:
  shows "\<exists> A1 A2 B1 B2 C1 C2. 
A1 A2 Par B1 B2 \<and> B1 B2 Par C1 C2 \<and> \<not> (A1 A2 Par C1 C2)" 
  using NPost05 Postulate05_def
    postulate_of_transitivity_of_parallelism_def by blast

lemma NPost06:
  shows "\<not> Postulate06" 
  by (simp add: NPost02 equivalent_postulates_without_decidability_of_intersection_of_lines)

theorem not_midpoint_converse_postulate_thm:
  shows "\<exists> A B C P Q.
  \<not> Col A B C \<and> P Midpoint B C \<and> A B Par Q P \<and> Col A C Q \<and> \<not> Q Midpoint A C" 
  using NPost06 midpoint_converse_postulate_def 
    Postulate06_def by blast

lemma NPost07:
  shows "\<not> Postulate07" 
  using NPost02 equivalent_postulates_without_decidability_of_intersection_of_lines by blast

theorem not_alternate_interior_angles_postulate_thm:
  shows "\<exists> A B C D. A C TS B D \<and> A B Par C D \<and> \<not> B A C CongA D C A"
  using NPost07 Postulate07_def alternate_interior_angles_postulate_def by blast

lemma NPost08:
  shows "\<not> Postulate08" 
  using NPost06 equivalent_postulates_without_decidability_of_intersection_of_lines by blast

theorem not_consecutive_interior_angles_postulate_thm:
  shows "\<exists> A B C D. B C OS A D \<and> A B Par C D \<and> \<not> A B C SuppA B C D" 
  using NPost08 Postulate08_def consecutive_interior_angles_postulate_def by blast

lemma NPost09:
  shows "\<not> Postulate09" 
  by (simp add: NPost02 equivalent_postulates_without_decidability_of_intersection_of_lines)

theorem not_perpendicular_transversal_postulate_thm:
  shows "\<exists> A B C D P Q. A B Par C D \<and> A B Perp P Q \<and> 
Coplanar C D P Q \<and> \<not> C D Perp P Q" 
  using NPost09 Postulate09_def perpendicular_transversal_postulate_def by blast

lemma NPost10:
  shows "\<not> Postulate10" 
  using NPost05 equivalent_postulates_without_decidability_of_intersection_of_lines by blast

theorem not_postulate_of_parallelism_of_perpendicular_transversals_thm:
  shows "\<exists> A1 A2 B1 B2 C1 C2 D1 D2.
   A1 A2 Par B1 B2 \<and> A1 A2 Perp C1 C2 \<and> B1 B2 Perp D1 D2 \<and>
   Coplanar A1 A2 C1 D1 \<and> Coplanar A1 A2 C1 D2 \<and>
   Coplanar A1 A2 C2 D1 \<and> Coplanar A1 A2 C2 D2 \<and> \<not> C1 C2 Par D1 D2" 
  using NPost10 Postulate10_def 
    postulate_of_parallelism_of_perpendicular_transversals_def by blast

lemma NPost11:
  shows "\<not> Postulate11" 
  using NPost02 equivalent_postulates_without_decidability_of_intersection_of_lines by fastforce

theorem not_universal_posidonius_postulate:
  shows "\<exists> A1 A2 A3 A4 B1 B2 B3 B4.
   A1 A2 Par B1 B2 \<and> Col A1 A2 A3 \<and> Col B1 B2 B3 \<and> A1 A2 Perp A3 B3 \<and>
   Col A1 A2 A4 \<and> Col B1 B2 B4 \<and> A1 A2 Perp A4 B4 \<and> \<not> Cong A3 B3 A4 B4" 
  using NPost11 Postulate11_def universal_posidonius_postulate_def by blast

lemma NPost12:
  shows "\<not> Postulate12" 
  using NPost02 Postulate02_def Postulate12_def playfair_bis__playfair by blast

theorem not_alternative_playfair_s_postulate_thm:
  shows "\<exists> A1 A2 B1 B2 C1 C2 P.
     P Perp2 A1 A2 B1 B2 \<and> \<not> Col A1 A2 P \<and> Col P B1 B2 \<and> 
     Coplanar A1 A2 B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 \<and> 
     (\<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2)" 
  using NPost02 Postulate02_def alternative_playfair_s_postulate_def 
    playfair_bis__playfair by blast

lemma NPost13:
  shows "\<not> Postulate13" 
  using Cycle_2 NPost01 by blast

theorem not_proclus_postulate_thm:
  shows "\<exists> A B C D P Q. (\<forall> Y. A B Par C D \<and> Col A B P \<and> 
\<not> Col A B Q \<and> Coplanar C D P Q \<and> (\<not> Col P Q Y \<or> \<not> Col C D Y))" 
  using NPost13 proclus_postulate_def Postulate13_def by blast

lemma NPost14:
  shows "\<not> Postulate14" 
  using Cycle_2 NPost13 by blast

theorem not_alternative_proclus_postulate_thm:
  shows "\<exists> A B C D P Q. (\<forall> Y. P Perp2 A B C D \<and> 
\<not> Col C D P \<and> Coplanar A B C D \<and> Col A B P \<and> 
    \<not> Col A B Q \<and> Coplanar C D P Q \<and> (\<not> Col P Q Y \<or> \<not> Col C D Y))"
  using NPost14 alternative_proclus_postulate_def Postulate14_def by blast

lemma NPost15:
  shows "\<not> Postulate15" 
  using Cycle_1 NPost02 by blast

theorem not_triangle_circumscription_principle_thm:
  shows "\<exists> A B C. \<forall> D. (\<not> Col A B C \<and> 
(\<not> Cong A D B D \<or> \<not> Cong A D C D \<or> \<not> Coplanar A B C D))" 
  using NPost15 Postulate15_def 
    triangle_circumscription_principle_def by blast

lemma NPost16:
  shows "\<not> Postulate16" 
  using Cycle_2 NPost01 by blast

theorem not_inverse_projection_postulate_thm:
  shows "\<exists> A B C P Q. \<forall> Y.
     Acute A B C \<and> B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q \<and>
(\<not> B Out C Y \<or> \<not> Col P Q Y)" 
  using NPost16 Postulate16_def inverse_projection_postulate_def by blast

lemma NPost17:
  shows "\<not> Postulate17" 
  using Cycle_2 NPost01 by blast

theorem not_euclid_5_thm:
  shows "\<exists> P Q R S T U. \<forall> I.
     BetS P T Q \<and> BetS R T S \<and> BetS Q U R \<and> \<not> Col P Q S \<and> 
Cong P T Q T \<and> Cong R T S T \<and> (\<not> BetS S Q I \<or> \<not> BetS P U I)"
  using NPost17 Postulate17_def euclid_5_def by blast

lemma NPost18:
  shows "\<not> Postulate18" 
  using Cycle_2 NPost01 by blast

theorem not_strong_parallel_postulate_thm:
  shows "\<exists> P Q R S T U. \<forall> I.
    BetS P T Q \<and> BetS R T S \<and> \<not> Col P R U \<and> Coplanar P Q R U \<and> 
    Cong P T Q T \<and> Cong R T S T \<and> (\<not> Col S Q I \<or> \<not> Col P U I)" 
  using NPost18 Postulate18_def strong_parallel_postulate_def by blast

lemma NPost19:
  shows "\<not> Postulate19" 
  using Cycle_2 NPost01 by blast

theorem not_alternative_strong_parallel_postulate_thm:
  shows "\<exists> A B C D P Q R. \<forall> Y.
   B C OS A D \<and> A B C B C D SumA P Q R \<and> \<not> Bet P Q R
\<and> (\<not> Col B A Y \<or> \<not> Col C D Y)" 
  using NPost19 Postulate19_def alternative_strong_parallel_postulate_def by blast

lemma NPost20:
  shows "\<not> Postulate20" 
  using Cycle_2 NPost01 by blast

theorem not_euclid_s_parallel_postulate_thm:
  shows "\<exists> A B C D P Q R. \<forall> Y.
     B C OS A D \<and> SAMS A B C B C D \<and> A B C B C D SumA P Q R \<and> 
\<not> Bet P Q R \<and> (\<not> B Out A Y \<or> \<not> C Out D Y)" 
  using NPost20 Postulate20_def euclid_s_parallel_postulate_def by blast

end

subsection "Tarski non euclidean (with Greenberg axiom)"

context Tarski_Greenberg_Non_Euclidean

begin

lemma Greenberg_s_axiom_thm:
  shows "Axiom4" 
  using Axiom4_def greenberg greenberg_s_axiom_def by blast

lemma NPost03:
  shows "\<not> Postulate03" 
  using Greenberg_s_axiom_thm InterCycle1 NPost02 Postulate02_def 
    Postulate12_def playfair_bis__playfair by blast

theorem not_triangle_postulate_thm:
  shows "\<exists> A B C D E F. A B C TriSumA D E F \<and> \<not> Bet D E F"
  using NPost03 Postulate03_def triangle_postulate_def by blast

lemma NPost21:
  shows "\<not> Postulate21" 
  using Cycle_3 Greenberg_s_axiom_thm NPost03 by blast

theorem not_postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights_thm:
  shows "\<forall> A B C D E F. A B C TriSumA D E F \<and> Bet D E F \<longrightarrow> Col A B C"
  using NPost21 Postulate21_def 
    postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights_def by blast

lemma NPost22:
  shows "\<not> Postulate22"  
  using Cycle_3 Greenberg_s_axiom_thm NPost21 by blast

theorem not_posidonius_postulate_thm:
  shows "\<forall> A1 A2 B1 B2.
 Col A1 A2 B1 \<or> B1 = B2 \<or> \<not> Coplanar A1 A2 B1 B2 \<or>
    (\<exists> A3 A4 B3 B4.
              Col A1 A2 A3 \<and> Col B1 B2 B3 \<and> A1 A2 Perp A3 B3 \<and>
              Col A1 A2 A4 \<and> Col B1 B2 B4 \<and> A1 A2 Perp A4 B4 \<and> 
        \<not> Cong A3 B3 A4 B4) "
  using NPost22 Postulate22_def posidonius_postulate_def by blast

theorem not_posidonius_postulate_thm_1:
  shows "\<forall> A1 A2 B.
 Col A1 A2 B \<or> (\<exists> A3 A4 B3 B4.
              Col A1 A2 A3 \<and> Col B B B3 \<and> A1 A2 Perp A3 B3 \<and>
              Col A1 A2 A4 \<and> Col B B B4 \<and> A1 A2 Perp A4 B4 \<and> 
        \<not> Cong A3 B3 A4 B4)"
proof -
  {
    fix A1 A2 B
    have "Coplanar A1 A2 B B" 
      using ncop_distincts by blast
    assume "\<not> Col A1 A2 B" 
    hence "    (\<exists> A3 A4 B3 B4.
              Col A1 A2 A3 \<and> Col B B B3 \<and> A1 A2 Perp A3 B3 \<and>
              Col A1 A2 A4 \<and> Col B B B4 \<and> A1 A2 Perp A4 B4 \<and> 
        \<not> Cong A3 B3 A4 B4)" 
      by (metis(full_types) col_trivial_1 ncop_distincts not_posidonius_postulate_thm)
  }
  thus ?thesis 
    by blast
qed

lemma NPost23:
  shows "\<not> Postulate23" 
  using Cycle_3 NPost21 Greenberg_s_axiom_thm by blast

theorem not_postulate_of_existence_of_similar_triangles_thm:
  shows "\<forall> A B C D E F. 
  (Col A B C \<or> Cong A B D E \<or> \<not> A B C CongA D E F \<or>
   \<not> B C A CongA E F D \<or> \<not> C A B CongA F D E)"
  using NPost23 Postulate23_def postulate_of_existence_of_similar_triangles_def by blast

lemma NPost24:
  shows "\<not> Postulate24" 
  using Cycle_3 NPost21 Greenberg_s_axiom_thm by blast

theorem not_thales_postulate_thm:
  shows "\<exists> A B C M.
   M Midpoint A B \<and> Cong M A M C \<and> \<not> Per A C B" 
  using NPost24 Postulate24_def thales_postulate_def by blast

lemma NPost25:
  shows "\<not> Postulate25" 
  using Cycle_3 NPost21 Greenberg_s_axiom_thm by blast

theorem not_thales_converse_postulate_thm:
  shows "\<exists> A B C M. M Midpoint A B \<and> Per A C B \<and> \<not> Cong M A M C" 
  using NPost25 Postulate25_def thales_converse_postulate_def by blast

lemma NPost26:
  shows "\<not> Postulate26" 
  using Cycle_3 NPost22 Greenberg_s_axiom_thm by blast

theorem not_existential_thales_postulate_thm:
  shows "\<forall> A B C M. (M Midpoint A B \<and> Cong M A M C \<and> Per A C B) \<longrightarrow> Col A B C"
  using NPost26 Postulate26_def existential_thales_postulate_def by blast

lemma NPost27:
  shows "\<not> Postulate27" 
  using Cycle_3 NPost22 Greenberg_s_axiom_thm by fastforce

theorem not_postulate_of_right_saccheri_quadrilaterals_thm:
  shows "\<exists> A B C D. Saccheri A B C D \<and> \<not> Per A B C" 
  using Cycle_3 NPost03 Postulate28_def ex_saccheri
    postulate_of_existence_of_a_right_saccheri_quadrilateral_def by blast

lemma NPost28:
  shows "\<not> Postulate28" 
  using Cycle_3 NPost03 Greenberg_s_axiom_thm by blast

theorem not_postulate_of_existence_of_a_right_saccheri_quadrilateral_thm:
  shows "\<forall> A B C D. \<not> (Saccheri A B C D \<and> Per A B C)" 
  using Cycle_3 NPost26 Postulate28_def
    postulate_of_existence_of_a_right_saccheri_quadrilateral_def by blast

lemma NPost29:
  shows "\<not> Postulate29" 
  using Cycle_3 NPost27 Greenberg_s_axiom_thm by blast

theorem not_postulate_of_right_lambert_quadrilaterals_thm:
  shows "\<exists> A B C D. Lambert A B C D \<and> \<not> Per B C D" 
  using Cycle_3 NPost26 Postulate30_def postulate_of_right_lambert_quadrilaterals_def 
    rectangle_principle__rectangle_existence by blast

lemma NPost30:
  shows "\<not> Postulate30" 
  using Cycle_3 NPost03 Greenberg_s_axiom_thm by blast

theorem not_postulate_of_existence_of_a_right_lambert_quadrilateral_thm:
  shows "\<forall> A B C D. \<not> (Lambert A B C D \<and> Per B C D)" 
  using Cycle_3 NPost29 Postulate30_def 
    postulate_of_existence_of_a_right_lambert_quadrilateral_def by blast

end
end


