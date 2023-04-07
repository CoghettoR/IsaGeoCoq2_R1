(* IsageoCoq2_R1

Tarski_Continuity_Neutral.thy

Version 2.2.0 IsaGeoCoq2_R1, Port part of GeoCoq 3.4.0
Version 2.1.0 IsaGeoCoq2_R1, Port part of GeoCoq 3.4.0
Copyright (C) 2021-2023 Roland Coghetto roland.coghetto ( a t ) cafr-msa2p.be
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
theory Tarski_Continuity_Neutral

imports
  Tarski_Neutral

begin

(*>*)

context Tarski_neutral_dimensionless
begin

subsection "Circle"

subsubsection "Circle-Def"
  (** P is on the circle of center A going through B *)

definition OnCircle ::
  "[TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("_ OnCircle _ _ " [99,99,99] 50)
  where
    "P OnCircle A B  \<equiv> Cong A P A B"

(** P is inside or on the circle of center A going through B *)
definition InCircle ::
  "[TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("_ InCircle _ _ " [99,99,99] 50)
  where
    "P InCircle A B  \<equiv> A P Le A B"

(** P is outside or on the circle of center A going through B *)
definition OutCircle ::
  "[TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("_ OutCircle _ _ " [99,99,99] 50)
  where
    "P OutCircle A B  \<equiv> A B Le A P"

(** P is strictly inside the circle of center A going through B *)

definition InCircleS ::
  "[TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("_ InCircleS _ _ " [99,99,99] 50)
  where
    "P InCircleS A B  \<equiv> A P Lt A B"

(** P is strictly outside the circle of center A going through B *)

definition OutCircleS ::
  "[TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("_ OutCircleS _ _ " [99,99,99] 50)
  where
    "P OutCircleS A B  \<equiv> A B Lt A P"

(** The line segment AB is a diameter of the circle of center O going through P *)

definition Diam ::
  "[TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("Diam _ _ _ _ " [99,99,99,99] 50)
  where
    "Diam A B PO P \<equiv> Bet A PO B \<and> A OnCircle PO P \<and> B OnCircle PO P"

definition EqC ::
  "[TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("EqC _ _ _ _ " [99,99,99,99] 50)
  where
    "EqC A B C D \<equiv>
 \<forall> X. (X OnCircle A B \<longleftrightarrow> X OnCircle C D)"


(** The circles of center A passing through B and
                of center C passing through D intersect
                in two distinct points P and Q. *)

definition InterCCAt ::
  "[TPoint,TPoint,TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("InterCCAt _ _ _ _ _ _ " [99,99,99,99,99,99] 50)
  where
    "InterCCAt A B C D P Q \<equiv>
  \<not> EqC A B C D \<and>
  P \<noteq> Q \<and> P OnCircle C D \<and> Q OnCircle C D \<and> P OnCircle A B \<and> Q OnCircle A B"

(** The circles of center A passing through B and
                of center C passing through D
                have two distinct intersections. *)
definition InterCC ::
  "[TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("InterCC _ _ _ _ " [99,99,99,99] 50)
  where
    "InterCC A B C D \<equiv> \<exists> P Q. InterCCAt A B C D P Q"

(** The circles of center A passing through B and
                of center C passing through D
                are tangent. *)
definition TangentCC ::
  "[TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("TangentCC _ _ _ _ " [99,99,99,99] 50)
  where
    "TangentCC A B C D \<equiv> \<exists>\<^sub>\<le>\<^sub>1 X. X OnCircle A B \<and> X OnCircle C D"

(** The line AB is tangent to the circle OP *)

definition Tangent ::
  "[TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("Tangent _ _ _ _ " [99,99,99,99] 50)
  where 
    "Tangent A B PO P \<equiv> \<exists>\<^sub>\<le>\<^sub>1 X. Col A B X \<and> X OnCircle PO P" 

definition TangentAt ::
  "[TPoint,TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("TangentAt _ _ _ _ _ " [99,99,99,99,99] 50)
  where
    "TangentAt A B PO P T \<equiv>
  Tangent A B PO P \<and> Col A B T \<and> T OnCircle PO P"

(** The points A, B, C and D belong to a same circle *)

definition Concyclic ::
  "[TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("Concyclic _ _ _ _ " [99,99,99,99] 50)
  where
    "Concyclic A B C D \<equiv> Coplanar A B C D \<and>
  (\<exists> PO P. A OnCircle PO P \<and> B OnCircle PO P \<and> 
C OnCircle PO P \<and> D OnCircle PO P)"

(** The points A, B, C and D are concyclic or lined up *)

definition ConcyclicGen ::
  "[TPoint,TPoint,TPoint,TPoint] \<Rightarrow> bool"
  ("ConcyclicGen _ _ _ _ " [99,99,99,99] 50)
  where
    "ConcyclicGen A B C D \<equiv>
  Concyclic A B C D \<or> 
(Col A B C \<and> Col A B D \<and> Col A C D \<and> Col B C D)"

subsubsection "Circle Propositions"

lemma inc112:
  shows "A InCircle A B" 
  by (meson InCircle_def l5_5_2 not_bet_distincts segment_construction_0)

lemma onc212:
  shows "B OnCircle A B" 
  by (simp add: OnCircle_def cong_reflexivity)

lemma onc_sym:
  assumes "P OnCircle A B"
  shows "B OnCircle A P" 
  using Cong_cases OnCircle_def assms by auto

lemma ninc__outcs:
  assumes "\<not> (X InCircle PO P)"
  shows "X OutCircleS PO P" 
  using nle__lt InCircle_def OutCircleS_def assms by blast

lemma inc__outc_1: 
  assumes "P InCircle A B"
  shows "B OutCircle A P" 
  using InCircle_def OutCircle_def assms by blast

lemma inc__outc_2: 
  assumes "B OutCircle A P"
  shows "P InCircle A B" 
  using InCircle_def OutCircle_def assms by blast

lemma inc__outc: 
  shows "P InCircle A B \<longleftrightarrow> B OutCircle A P" 
  by (simp add: InCircle_def OutCircle_def)

lemma incs__outcs_1:
  assumes "P InCircleS A B"
  shows "B OutCircleS A P"   
  using InCircleS_def OutCircleS_def assms by blast

lemma incs__outcs_2: 
  assumes "B OutCircleS A P"
  shows "P InCircleS A B" 
  using InCircleS_def OutCircleS_def assms by blast

lemma incs__outcs:
  shows "P InCircleS A B \<longleftrightarrow> B OutCircleS A P" 
  using incs__outcs_1 incs__outcs_2 by blast

lemma onc__inc: 
  assumes "P OnCircle A B"
  shows "P InCircle A B" 
  using InCircle_def OnCircle_def assms cong__le by blast

lemma onc__outc: 
  assumes "P OnCircle A B"
  shows "P OutCircle A B" 
  by (simp add: assms inc__outc_1 onc__inc onc_sym)

lemma inc_outc__onc: 
  assumes "P InCircle A B" and
    "P OutCircle A B"
  shows "P OnCircle A B" 
  using InCircle_def OnCircle_def OutCircle_def assms(1) assms(2) le_anti_symmetry by blast

lemma incs__inc: 
  assumes "P InCircleS A B"
  shows "P InCircle A B" 
  using InCircle_def InCircleS_def Lt_def assms by blast

lemma outcs__outc: 
  assumes "P OutCircleS A B"
  shows "P OutCircle A B" 
  using assms inc__outc incs__inc incs__outcs by blast

lemma incs__noutc_1:
  assumes "P InCircleS A B"
  shows "\<not> P OutCircle A B" 
  using InCircleS_def OutCircle_def assms le__nlt by blast

lemma incs__noutc_2:
  assumes "\<not> P OutCircle A B"
  shows "P InCircleS A B" 
  using assms inc__outc_1 incs__outcs_2 ninc__outcs by blast

lemma incs__noutc:
  shows "P InCircleS A B \<longleftrightarrow> \<not> P OutCircle A B" 
  using incs__noutc_1 incs__noutc_2 by blast

lemma outcs__ninc_1: 
  assumes "P OutCircleS A B"
  shows "\<not> P InCircle A B" 
  by (simp add: assms inc__outc incs__noutc_1 incs__outcs_2)

lemma outcs__ninc_2: 
  assumes "\<not> P InCircle A B" 
  shows "P OutCircleS A B" 
  by (simp add: assms ninc__outcs)

lemma outcs__ninc: 
  shows "P OutCircleS A B \<longleftrightarrow> \<not> P InCircle A B" 
  using inc__outc_1 incs__noutc_1 incs__outcs_2 ninc__outcs by blast

lemma inc__noutcs_1: 
  assumes "P InCircle A B"
  shows "\<not> P OutCircleS A B" 
  using assms outcs__ninc_1 by blast

lemma inc__noutcs_2: 
  assumes "\<not> P OutCircleS A B" 
  shows "P InCircle A B" 
  using assms outcs__ninc_2 by blast

lemma inc__noutcs: 
  "P InCircle A B \<longleftrightarrow> \<not> P OutCircleS A B" 
  by (simp add: outcs__ninc)

lemma outc__nincs_1:
  assumes "P OutCircle A B"
  shows "\<not> P InCircleS A B" 
  using assms incs__noutc_1 by blast

lemma outc__nincs_2:
  assumes "\<not> P InCircleS A B" 
  shows "P OutCircle A B" 
  using assms incs__noutc by blast

lemma outc__nincs:
  shows "P OutCircle A B \<longleftrightarrow> \<not> P InCircleS A B" 
  using incs__noutc by force

lemma inc_eq: 
  assumes "P InCircle A A"
  shows "A = P" 
  by (metis OnCircle_def assms bet_cong_eq between_trivial2 inc112 inc__outc inc_outc__onc)

lemma outc_eq: 
  assumes "A OutCircle A B"
  shows "A = B" 
  by (meson OnCircle_def assms bet_cong_eq between_trivial2 inc112 inc_outc__onc)

lemma onc2__cong:
  assumes "A OnCircle PO P" and
    "B OnCircle PO P"
  shows "Cong PO A PO B" 
  by (meson OnCircle_def assms(1) assms(2) cong_transitivity onc_sym)

(** If a point is strictly inside a segment of a disk, it is strictly inside the circle. *)

lemma bet_inc2__incs:
  assumes "X \<noteq> U" and
    "X \<noteq> V" and
    "Bet U X V" and
    "U InCircle PO P" and
    "V InCircle PO P" 
  shows "X InCircleS PO P" 
proof -
  {
    assume "PO U Le PO V"
    hence "PO X Lt PO V" 
      using Le_cases assms(1) assms(2) assms(3) bet_le__lt lt_comm by blast
    hence "X InCircleS PO P" 
      using InCircleS_def InCircle_def assms(5) le3456_lt__lt by blast
  }
  moreover
  {
    assume "PO V Le PO U"
    hence "PO X Lt PO U" 
      using assms(1) assms(2) assms(3) bet_le__lt between_symmetry le_comm lt_comm by blast
    hence "X InCircleS PO P" 
      by (meson InCircle_def OutCircle_def assms(4) le__nlt le_transitivity outc__nincs_2)
  }
  ultimately show ?thesis 
    using local.le_cases by blast
qed

lemma bet_incs2__incs:
  assumes "Bet U X V" and
    "U InCircleS PO P" and
    "V InCircleS PO P" 
  shows "X InCircleS PO P" 
  by (metis assms(1) assms(2) assms(3) bet_inc2__incs incs__inc)

(** If A and B are two points inside the circle, then all points on the segment AB are also
    in the circle, i.e. a circle is a convex figure.
*)

lemma bet_inc2__inc:
  assumes "U InCircle A B" and
    "V InCircle A B" and
    "Bet U P V"
  shows "P InCircle A B" 
  by (metis assms(1) assms(2) assms(3) bet_inc2__incs incs__inc)

(** Given two points U and V on a circle, the points of the line UV which are inside 
the circle are between U and V. *) 

lemma col_inc_onc2__bet:
  assumes "U \<noteq> V" and
    "U OnCircle A B" and
    "V OnCircle A B" and
    "Col U V P" and
    "P InCircle A B"
  shows "Bet U P V" 
proof (cases "P = U")
  case True
  thus ?thesis 
    by (simp add: between_trivial2)
next
  case False
  hence "P \<noteq> U" 
    by simp
  show ?thesis 
  proof (cases "P = V")
    case True
    thus ?thesis 
      using between_trivial by force
  next
    case False
    hence "P \<noteq> V" 
      by simp
    have "Cong A U A V" 
      using assms(2) assms(3) onc2__cong by auto
    have "U Out P V" 
      by (metis Col_cases \<open>P \<noteq> U\<close> assms(1) assms(2) assms(3) assms(4) 
          assms(5) bet_inc2__incs incs__noutc_1 onc__inc onc__outc or_bet_out)
    moreover have "V Out U P" 
      by (metis False assms(2) assms(3) assms(4) assms(5) bet_inc2__incs 
          calculation l6_3_1 onc__inc onc__outc or_bet_out outc__nincs)
    ultimately show ?thesis 
      using out2__bet by blast
  qed
qed

(** Given two points U and V on a circle, all points of line UV which are outside 
the segment UV are outside the circle. *)

lemma onc2_out__outcs:
  assumes "U \<noteq> V" and
    "U OnCircle A B" and
    "V OnCircle A B" and
    "P Out U V"
  shows "P OutCircleS A B" 
  by (meson Col_cases assms(1) assms(2) assms(3) assms(4) 
      col_inc_onc2__bet not_bet_and_out out_col outcs__ninc_2)

(** Given two points U and V inside a circle, all points of line UV which are outside 
the circle are outside the segment UV. *)

lemma col_inc2_outcs__out:
  assumes "U InCircle A B" and
    "V InCircle A B" and
    "Col U V P" and
    "P OutCircleS A B"
  shows "P Out U V" 
  by (meson Col_cases assms(1) assms(2) assms(3) assms(4) 
      bet_inc2__inc or_bet_out outcs__ninc_1)

(** If the center of a circle belongs to a chord, then it is the midpoint of the chord. *)

lemma col_onc2__mid: 
  assumes "U \<noteq> V" and
    "U OnCircle A B" and
    "V OnCircle A B" and
    "Col U V A"
  shows "A Midpoint U V" 
  using Col_cases assms(1) assms(2) assms(3) assms(4) l7_20 onc2__cong by blast

(** Given a point U on a circle and a point P inside the circle, there is a point V such as
    UV is a chord of the circle going through P. *)

lemma chord_completion: 
  assumes "U OnCircle A B" and
    "P InCircle A B"
  shows "\<exists> V. V OnCircle A B \<and> Bet U P V" 
proof (cases "U = A")
  case True
  then show ?thesis 
    using OnCircle_def assms(1) assms(2) between_trivial2 
      cong_reverse_identity inc_eq by blast
next
  case False
  hence "U \<noteq> A"
    by simp
  have "\<exists> A'. U \<noteq> A' \<and> Col U P A' \<and> Per A A' U" 
  proof (cases "Col U P A")
    case True
    thus ?thesis 
      using False l8_20_1_R1 by blast
  next
    case False
    hence "\<not> Col U P A" 
      by simp
    obtain A' where "Col U P A'" and "U P Perp A A'" 
      using False l8_18_existence by blast
    {
      assume "U = A'"
      have "U \<noteq> P" 
        using False not_col_distincts by auto
      have "Per P U A \<or> Obtuse P U A" 
        using Perp_perm \<open>U = A'\<close> \<open>U P Perp A A'\<close> perp_per_2 by blast
      hence "U A Lt P A" 
        using \<open>U \<noteq> A\<close> \<open>U \<noteq> P\<close> l11_46 by auto
      hence False 
        by (meson Cong_cases InCircleS_def OnCircle_def assms(1) assms(2) 
            cong2_lt__lt cong_reflexivity inc__outc incs__noutc)
    }
    hence "U \<noteq> A'" 
      by auto
    moreover have "Per A A' U" 
      using \<open>Col U P A'\<close> \<open>U P Perp A A'\<close> col_trivial_3 l8_16_1 by blast
    ultimately show ?thesis 
      using \<open>Col U P A'\<close> by blast
  qed
  then obtain A' where "U \<noteq> A'" and "Col U P A'" and "Per A A' U" 
    by auto
  obtain V where "A' Midpoint U V" 
    using symmetric_point_construction by auto
  hence "Cong A U A V" 
    using \<open>Per A A' U\<close> per_double_cong by auto
  hence "V OnCircle A B" 
    using OnCircle_def assms(1) cong_inner_transitivity by blast
  have "Col U V P" 
    by (meson Midpoint_def \<open>A' Midpoint U V\<close> \<open>Col U P A'\<close> \<open>U \<noteq> A'\<close> 
        bet_col col_permutation_5 col_transitivity_1)
  thus ?thesis using col_inc_onc2__bet 
    by (metis \<open>A' Midpoint U V\<close> \<open>U \<noteq> A'\<close> \<open>V OnCircle A B\<close> 
        assms(1) assms(2) midpoint_distinct_2)
qed

(** Given a circle, there is a point strictly outside the circle. *)

lemma outcs_exists: 
  shows "\<exists> Q. Q OutCircleS PO P" 
  by (meson bet_inc2__incs inc__noutcs_2 incs__outcs point_construction_different)

(** Given a circle of center O and a ray OX, there is a point on the ray
    which is also strictly outside the circle. *)

lemma outcs_exists1: 
  assumes "X \<noteq> PO"
  shows "\<exists> Q. PO Out X Q \<and> Q OutCircleS PO P" 
proof -
  obtain Q where "Bet PO X Q" and "Cong X Q PO P"
    using segment_construction by blast
  have "PO Out X Q" 
    using \<open>Bet PO X Q\<close> assms bet_out by auto
  moreover have "\<not> Cong PO P PO Q" 
    using \<open>Bet PO X Q\<close> \<open>Cong X Q PO P\<close> assms bet_cong_eq between_trivial 
      cong_transitivity by blast
  hence "Q OutCircleS PO P" 
    using OutCircleS_def by (meson Bet_cases \<open>Bet PO X Q\<close> \<open>Cong X Q PO P\<close> 
        assms bet__lt1213 cong2_lt__lt cong_pseudo_reflexivity not_cong_1243)
  ultimately show ?thesis 
    by auto
qed

(** Given a circle there is a point which is strictly inside. *)

lemma incs_exists:
  assumes "PO \<noteq> P"
  shows "\<exists> Q. Q InCircleS PO P" 
  using assms incs__noutc outc_eq by blast

(** Given a circle of center O and a ray OX, there is a point on the ray
    which is also strictly inside the circle. *)

lemma incs_exists1: 
  assumes "X \<noteq> PO" and
    "P \<noteq> PO"
  shows "\<exists> Q. PO Out X Q \<and> Q InCircleS PO P" 
proof -
  obtain M where "M Midpoint PO P"
    using midpoint_existence by blast
  obtain Q where "PO Out X Q" and "Cong PO Q PO M" 
    by (metis Midpoint_def \<open>M Midpoint PO P\<close> assms(1) assms(2) between_cong_2
        between_trivial2 point_construction_different segment_construction_3)
  have "PO M Lt PO P" 
    using \<open>M Midpoint PO P\<close> assms(2) mid__lt by presburger
  hence "Q InCircleS PO P" 
    using InCircleS_def \<open>Cong PO Q PO M\<close> cong2_lt__lt cong_reflexivity not_cong_3412 by blast
  thus ?thesis 
    using \<open>PO Out X Q\<close> by blast
qed

(** Given a circle of center O and a ray OX, there is a point on the ray 
which is also on the circle. *)

lemma onc_exists: 
  assumes "X \<noteq> PO" and
    "PO \<noteq> P"
  shows "\<exists> Q. Q OnCircle PO P \<and> PO Out X Q" 
  by (meson OnCircle_def assms(1) assms(2) l6_11_existence l6_6)

(** Given a circle of center O and a line OX, O is between two points of the line
    which are also on the circle. *)

lemma diam_points: 
  shows "\<exists> Q1 Q2. Bet Q1 PO Q2 \<and> Col Q1 Q2 X \<and> Q1 OnCircle PO P \<and> Q2 OnCircle PO P" 
proof (cases "P = PO")
  case True
  thus ?thesis 
    using between_trivial col_trivial_1 onc212 by blast
next
  case False
  hence "P \<noteq> PO" 
    by simp
  show ?thesis 
  proof (cases "X = PO")
    case True
    thus ?thesis 
      by (meson Col_def OnCircle_def between_symmetry segment_construction)
  next
    case False
    hence "X \<noteq> PO"
      by simp
    obtain Q1 where "Q1 OnCircle PO P" and "PO Out X Q1" 
      using False \<open>P \<noteq> PO\<close> onc_exists by metis
    obtain Q2 where "Bet Q1 PO Q2" and "Cong PO Q2 PO Q1" 
      using segment_construction by blast
    have "Col Q1 Q2 X" 
      by (metis Col_def Out_cases \<open>Bet Q1 PO Q2\<close> \<open>PO Out X Q1\<close> 
          between_trivial2 col_transitivity_2 not_bet_and_out out_col)
    moreover have "Q2 OnCircle PO P" 
      by (meson OnCircle_def \<open>Cong PO Q2 PO Q1\<close> \<open>Q1 OnCircle PO P\<close> onc2__cong onc_sym)
    ultimately show ?thesis 
      using \<open>Bet Q1 PO Q2\<close> \<open>Q1 OnCircle PO P\<close> by blast
  qed
qed

(** The symmetric of a point on a circle relative to the center is also on the circle. *)

lemma symmetric_oncircle:
  assumes "PO Midpoint X Y" and
    "X OnCircle PO P"
  shows "Y OnCircle PO P" 
  by (meson OnCircle_def assms(1) assms(2) midpoint_cong not_cong_4312 onc2__cong onc_sym)

(** The middle of a chord together with the center of the circle and one end of the chord
    form a right angle *)

lemma mid_onc2__per:
  assumes "U OnCircle PO P" and
    "V OnCircle PO P" and
    "X Midpoint U V"
  shows "Per PO X U" 
  using Per_def assms(1) assms(2) assms(3) onc2__cong by blast

(** Euclid Book III Prop 3 (two lemmas).
 If a straight line passing through the center of a circle 
 bisects a straight line not passing through the center,
 then it also cuts it at right angles; and if it cuts it at right angles, then it also bisects it.
*)

(** The line from the center of a circle to the midpoint of a chord is perpendicular 
to the chord. *)

lemma mid_onc2__perp:
  assumes "PO \<noteq> X" and
    "A \<noteq> B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "X Midpoint A B"
  shows "PO X Perp A B" 
proof -
  have "Per PO X A" 
    using assms(3) assms(4) assms(5) mid_onc2__per by blast
  thus ?thesis 
    by (metis Perp_cases assms(1) assms(2) assms(5) col_per_perp 
        is_midpoint_id midpoint_col)
qed

(** If a line passing through the center of a circle is perpendicular to a chord,
    then they intersect at the middle of the chord *)

lemma col_onc2_perp__mid:
  assumes "PO \<noteq> X" and
    "A \<noteq> B" and
    "Col A B X" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "PO X Perp A B" 
  shows "X Midpoint A B" 
proof -
  obtain M  where "M Midpoint A B" 
    using midpoint_existence by blast
  have "\<not> Col A B PO" 
    using assms(1) assms(3) assms(6) l8_14_1 perp_col2_bis by blast
  hence "PO \<noteq> M" 
    using \<open>M Midpoint A B\<close> midpoint_col not_col_permutation_2 by blast
  hence "A B Perp PO M" 
    using Perp_cases \<open>M Midpoint A B\<close>assms(2) assms(4) assms(5) mid_onc2__perp by blast
  hence "X = M" 
    by (meson NCol_cases Perp_perm \<open>M Midpoint A B\<close> assms(3) assms(6) 
        l8_18_uniqueness midpoint_col)
  thus ?thesis 
    by (simp add: \<open>M Midpoint A B\<close>)
qed

(** If two circles intersect at a point which is not on the line joining the center,
    then they intersect on any half-plane delimited by that line. *)

lemma circle_circle_os:
  assumes "I OnCircle A B" and
    "I OnCircle C D" and
    "\<not> Col A C I" and
    "\<not> Col A C P" 
  shows "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D \<and> A C OS P Z" 
proof -
  obtain X where "Col A C X" and "A C Perp I X" 
    using assms(3) l8_18_existence by fastforce
  obtain Z0 where "A C Perp Z0 X" and "A C OS P Z0" 
    using \<open>Col A C X\<close> assms(4) l10_15 by blast
  obtain Z where "X Out Z Z0" and "Cong X Z X I" 
    by (metis Out_def \<open>A C OS P Z0\<close> \<open>Col A C X\<close> assms(3) col_trivial_2 
        l6_11_existence l9_19)
  have "A C Perp X Z" 
    by (metis \<open>A C Perp Z0 X\<close> \<open>X Out Z Z0\<close> between_trivial 
        l6_6 not_bet_and_out out_col perp_col1 perp_right_comm)
  have "Cong A Z A I" 
  proof (cases "A = X")
    case True
    thus ?thesis 
      by (simp add: \<open>Cong X Z X I\<close>)
  next
    case False
    hence "A \<noteq> X" 
      by simp
    show ?thesis 
    proof (rule l10_12 [where ?B = "X" and ?B'="X"], insert \<open>Cong X Z X I\<close>)
      show "Per A X Z" 
        by (meson False \<open>A C Perp X Z\<close> \<open>Col A C X\<close> l8_16_1 not_col_distincts perp_col0)
      show "Per A X I" 
        by (metis NCol_cases \<open>A C Perp I X\<close> \<open>Col A C X\<close> col_trivial_2 l8_16_1 l8_2)
      show "Cong A X A X" 
        using cong_reflexivity by auto
    qed
  qed
  hence "Z OnCircle A B" 
    using OnCircle_def assms(1) cong_transitivity by blast
  moreover 
  have "Cong C Z C I" 
  proof -
    show ?thesis 
    proof (rule l10_12 [where ?B = "X" and ?B'="X"], insert \<open>Cong X Z X I\<close>)
      show "Per C X Z" 
        by (metis NCol_perm \<open>A C Perp X Z\<close> \<open>Col A C X\<close> col_trivial_3 l8_16_1 l8_2 perp_comm)
      show "Per C X I" 
        using \<open>A C Perp I X\<close> \<open>Col A C X\<close> col_trivial_2 l8_16_1 l8_2 by blast
      show "Cong C X C X" 
        by (simp add: cong_reflexivity)
    qed
  qed
  hence "Z OnCircle C D" 
    by (meson OnCircle_def assms(2) onc2__cong onc_sym)
  moreover 
  have "A C OS Z0 Z" 
    by (metis Out_def \<open>A C OS P Z0\<close> \<open>Col A C X\<close> \<open>X Out Z Z0\<close> col124__nos l9_19_R2)
  hence "A C OS P Z" 
    using \<open>A C OS P Z0\<close> one_side_transitivity by blast
  ultimately show ?thesis 
    by blast
qed

(** If two circles intersect, then they intersect on any plane containing the centers *)

lemma circle_circle_cop: 
  assumes "I OnCircle A B" and
    "I OnCircle C D"
  shows "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D \<and> Coplanar A C P Z" 
proof (cases "Col A C P")
  case True
  then show ?thesis 
    using assms(1) assms(2) ncop__ncol by blast
next
  case False
  hence "\<not> Col A C P" 
    by simp
  show ?thesis 
  proof (cases "Col A C I")
    case True
    then show ?thesis 
      using assms(1) assms(2) ncop__ncols by blast
  next
    case False
    obtain Z where "Z OnCircle A B" and "Z OnCircle C D" and "A C OS P Z" 
      using False \<open>\<not> Col A C P\<close> assms(1) assms(2) circle_circle_os by force
    moreover have "Coplanar A C P Z" 
      by (simp add: calculation(3) os__coplanar)
    ultimately show ?thesis 
      by blast
  qed
qed

(** A circle does not cut a line at more than two points. *)

lemma line_circle_two_points:
  assumes "U \<noteq> V" and
    "Col U V W" and
    "U OnCircle PO P" and
    "V OnCircle PO P" and
    "W OnCircle PO P" 
  shows "W = U \<or> W = V" 
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) 
      cong2__ncol not_cong_4321 onc2__cong)

(** The midpoint of a chord is strictly inside the circle. *)

lemma onc2_mid__incs:
  assumes "U \<noteq> V" and
    "U OnCircle PO P" and
    "V OnCircle PO P" and
    "M Midpoint U V"
  shows "M InCircleS PO P" 
  by (metis Midpoint_def assms(1) assms(2) assms(3) assms(4) 
      bet_inc2__incs midpoint_not_midpoint midpoint_out onc__inc out_diff1)

(** A point is either strictly inside, on or strictly outside a circle. *)

lemma circle_cases:
  shows "X OnCircle PO P \<or> X InCircleS PO P \<or> X OutCircleS PO P" 
  using inc_outc__onc outc__nincs_2 outcs__ninc_2 by blast

(** If a point is inside a circle, then it lies on a radius. *)

lemma inc__radius:
  assumes "X InCircle PO P"
  shows "\<exists> Y. Y OnCircle PO P \<and> Bet PO X Y" 
  by (meson Bet_cases OnCircle_def assms between_exchange3 
      chord_completion segment_construction)

lemma inc_onc2_out__eq:
  assumes "A InCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "A Out B C"
  shows "B = C" 
  using assms(1) assms(2) assms(3) assms(4) inc__noutcs_1 
    onc2_out__outcs by blast

lemma onc_not_center: 
  assumes "PO \<noteq> P" and
    "A OnCircle PO P"
  shows "A \<noteq> PO" 
  using OnCircle_def assms(1) assms(2) cong_reverse_identity by blast

lemma onc2_per__mid: 
  assumes "U \<noteq> V" and
    "M \<noteq> U" and
    "U OnCircle PO P" and
    "V OnCircle PO P" and
    "Col M U V" and
    "Per PO M U" 
  shows "M Midpoint U V" 
proof -
  obtain M' where "M' Midpoint U V" 
    using midpoint_existence by auto
  have "Per PO M' U" 
    using \<open>M' Midpoint U V\<close> assms(3) assms(4) mid_onc2__per by blast
  have "M = M' \<or> \<not> Col M' U V" 
    by (metis \<open>M' Midpoint U V\<close> \<open>Per PO M' U\<close> assms(1) assms(2) 
        assms(5) assms(6) col_per2_cases midpoint_distinct_3)
  hence "M = M'" 
    using \<open>M' Midpoint U V\<close> midpoint_col by auto
  thus ?thesis 
    by (simp add: \<open>M' Midpoint U V\<close>)
qed

(** Euclid Book III Prop 14
Equal straight lines in a circle are equally distant from the center, 
and those which are equally distant from the center equal one another.
*)

lemma cong_chord_cong_center:
  assumes "A OnCircle PO P" and 
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "D OnCircle PO P" and
    "M Midpoint A B" and
    "N Midpoint C D" and
    "Cong A B C D" 
  shows "Cong PO N PO M" 
proof -
  have "Cong M B N D" 
    by (meson assms(5) assms(6) assms(7) cong_commutativity cong_cong_half_1 l7_2)
  have "A M B PO IFSC C N D PO" 
    using IFSC_def \<open>Cong M B N D\<close> assms(1) assms(2) assms(3) assms(4) 
      assms(5) assms(6) assms(7) midpoint_bet not_cong_4321 onc2__cong by blast
  hence "Cong M PO N PO" 
    by (simp add: l4_2)
  thus ?thesis 
    using not_cong_4321 by blast
qed

(** variant *)
lemma cong_chord_cong_center1:
  assumes "A \<noteq> B" and 
    "C \<noteq> D" and 
    "M \<noteq> A" and 
    "N \<noteq> C" 
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "D OnCircle PO P" and
    "Col M A B" and
    "Col N C D" and
    "Per PO M A" and
    "Per PO N C" and
    "Cong A B C D" 
  shows "Cong PO N PO M" 
  using assms(1) assms(10) assms(11) assms(12) assms(13) assms(2) assms(3) 
    assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) 
    cong_chord_cong_center onc2_per__mid by presburger

(** Prop 7   **)

lemma onc_sym__onc:
  assumes "Bet PO A B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "X OnCircle PO P" and
    "X Y ReflectL A B" 
  shows "Y OnCircle PO P" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) 
    between_cong image_spec__eq onc2__cong by blast

lemma mid_onc__diam: 
  assumes "A OnCircle PO P" and
    "PO Midpoint A B" 
  shows "Diam A B PO P" 
  using Diam_def assms(1) assms(2) midpoint_bet symmetric_oncircle by blast

lemma chord_le_diam:
  assumes "Diam A B PO P" and
    "U OnCircle PO P" and
    "V OnCircle PO P"
  shows "U V Le A B" 
proof (rule triangle_inequality_2 [where ?B="PO" and ?B'="PO"])
  show "Bet A PO B" 
    using Diam_def assms(1) by auto
  show "Cong U PO A PO" 
    using Diam_def assms(1) assms(2) not_cong_4321 onc2__cong by blast
  show "Cong PO V PO B" 
    using Diam_def assms(1) assms(3) onc2__cong by auto
qed

lemma chord_lt_diam:
  assumes "\<not> Col PO U V" and
    "Diam A B PO P" and
    "U OnCircle PO P" and
    "V OnCircle PO P" 
  shows "U V Lt A B" 
proof -
  have "U V Le A B" 
    using assms(2) assms(3) assms(4) chord_le_diam by blast
  {
    assume "Cong U V A B" 
    obtain O' where "O' Midpoint U V" 
      using midpoint_existence by blast
    have "Cong PO A PO B" 
      using Diam_def assms(2) onc2__cong by blast
    hence "Cong A PO U O'" 
      by (meson Diam_def \<open>Cong U V A B\<close> \<open>O' Midpoint U V\<close> assms(2) 
          cong_cong_half_1 cong_symmetry midpoint_def not_cong_2134)
    hence "Cong B PO V O'" 
      by (meson Midpoint_def \<open>Cong PO A PO B\<close> \<open>O' Midpoint U V\<close>
          cong_4321 cong_right_commutativity cong_transitivity)
    have "Col PO U V" 
    proof (rule l4_13 [where ?A="PO" and ?B="A" and ?C="B"])
      show "Col PO A B" 
        using Col_def Diam_def assms(2) between_symmetry by blast
      show "PO A B Cong3 PO U V" 
        using Cong3_def Diam_def \<open>Cong U V A B\<close> assms(2) 
          assms(3) assms(4) cong_symmetry onc2__cong by blast
    qed
    hence False 
      by (simp add: assms(1))
  }
  thus ?thesis 
    using Lt_def \<open>U V Le A B\<close> by blast
qed

lemma inc2_le_diam:
  assumes "Diam A B PO P" and
    "U InCircle PO P" and
    "V InCircle PO P" 
  shows "U V Le A B" 
proof -
  have "Bet A PO B" and "A OnCircle PO P" and "B OnCircle PO P"
    using assms(1) Diam_def by auto
  obtain W where "Bet U PO W" and "Cong PO W PO V" 
    using segment_construction by blast
  have "U V Le U W" 
    using \<open>Bet U PO W\<close> \<open>Cong PO W PO V\<close> not_cong_3412 triangle_inequality by blast
  have "U W Le A B" 
  proof (rule bet2_le2__le [where ?P="PO" and ?Q="PO"], insert \<open>Bet A PO B\<close>)
    show "Bet U PO W" 
      by (simp add: \<open>Bet U PO W\<close>)
    show "PO U Le PO A" 
      by (meson InCircle_def OnCircle_def \<open>A OnCircle PO P\<close> 
          assms(2) between_trivial l5_5_2 le_transitivity onc_sym)
    show "PO W Le PO B" 
      by (meson InCircle_def OnCircle_def \<open>B OnCircle PO P\<close> 
          \<open>Cong PO W PO V\<close> assms(3) between_trivial l5_5_2 le_transitivity onc_sym)
  qed
  thus ?thesis 
    using \<open>U V Le U W\<close> le_transitivity by blast
qed

lemma onc_col_diam__eq: 
  assumes "Diam A B PO P" and
    "X OnCircle PO P" and
    "Col A B X" 
  shows "X = A \<or> X = B" 
  by (metis Diam_def assms(1) assms(2) assms(3) bet_neq21__neq 
      cong_reverse_identity line_circle_two_points onc2__cong)

lemma bet_onc_le_a: 
  assumes "Diam A B PO P" and
    "Bet B PO T" and
    "X OnCircle PO P"
  shows "T A Le T X" 
proof -
  have "Cong PO X PO A" 
    using Diam_def assms(1) assms(3) onc2__cong by blast
  show ?thesis
  proof (cases "PO = P")
    case True
    then show ?thesis 
      by (metis OnCircle_def \<open>Cong PO X PO A\<close> assms(3) 
          between_cong between_trivial2 cong_identity_inv le_reflexivity)
  next
    case False
    hence "PO \<noteq> P" 
      by simp
    show ?thesis 
    proof (cases "T = PO")
      case True
      then show ?thesis 
        by (simp add: \<open>Cong PO X PO A\<close> cong__le3412)
    next
      case False
      hence "PO Out T A" 
        by (metis Diam_def \<open>PO \<noteq> P\<close> assms(1) assms(2) between_symmetry l6_2 onc_not_center)
      thus ?thesis 
        using \<open>Cong PO X PO A\<close> triangle_reverse_inequality by auto
    qed
  qed
qed

lemma bet_onc_lt_a :
  assumes "Diam A B PO P" and
    "PO \<noteq> P" and
    "PO \<noteq> T" and
    "X \<noteq> A" and
    "Bet B PO T" and
    "X OnCircle PO P" 
  shows "T A Lt T X" 
proof -
  have "T A Le T X" 
    using assms(1) assms(5) assms(6) bet_onc_le_a by blast
  have "T A Lt T X \<or> Cong T A T X" 
    using Lt_def \<open>T A Le T X\<close> by auto
  {
    assume "Cong T A T X"
    have "Bet PO A T \<or> Bet PO T A" 
      by (metis Bet_cases Diam_def OnCircle_def assms(1) assms(2) assms(5) 
          between_cong between_trivial2 l5_2)
    moreover have "Cong PO A PO X" 
      using Diam_def assms(1) assms(6) onc2__cong by blast
    have "Bet PO A T \<longrightarrow> T A Lt T X" 
      using \<open>Cong PO A PO X\<close> \<open>Cong T A T X\<close> assms(4) l4_19 by blast
    moreover have "Bet PO T A \<longrightarrow> T A Lt T X" 
      by (metis Out_def \<open>Cong PO A PO X\<close> \<open>Cong T A T X\<close> assms(3) assms(4) 
          bet_out between_cong between_exchange4 l5_2 not_cong_3412 
          triangle_strict_reverse_inequality)
    ultimately have "T A Lt T X" 
      by blast
  }
  thus ?thesis 
    using \<open>T A Lt T X \<or> Cong T A T X\<close> by blast
qed

lemma bet_onc_le_b:
  assumes "Diam A B PO P" and
    "Bet A PO T" and
    "X OnCircle PO P" 
  shows "T X Le T A" 
  by (meson Bet_cases Diam_def assms(1) assms(2) assms(3) onc2__cong triangle_inequality)

lemma bet_onc_lt_b:
  assumes "Diam A B PO P" and
    "T \<noteq> PO" and
    "X \<noteq> A" and
    "Bet A PO T" and
    "X OnCircle PO P"  
  shows "T X Lt T A" 
proof -
  have "T X Le T A" 
    using assms(1) assms(4) assms(5) bet_onc_le_b by auto
  have "T X Lt T A \<or> Cong T A T X" 
    using Lt_def \<open>T X Le T A\<close> not_cong_3412 by blast
  moreover 
  {
    assume "Cong T A T X" 
    have "Bet T PO A" 
      using Bet_cases assms(4) by auto
    have "T PO A Cong3 T PO X" 
      using Cong3_def Diam_def \<open>Cong T A T X\<close> assms(1) assms(5) 
        cong_reflexivity onc2__cong by blast
    hence "Bet T PO X" 
      using l4_6 [where ?A="T" and ?B="PO" and ?C="A"] \<open>Bet T PO A\<close> by blast
    hence False 
      using Cong3_def \<open>Bet T PO A\<close> \<open>T PO A Cong3 T PO X\<close> 
        assms(2) assms(3) between_cong_3 by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma incs2_lt_diam:
  assumes "Diam A B PO P" and
    "U InCircleS PO P" and
    "V InCircleS PO P"
  shows "U V Lt A B" 
proof (cases "PO = P")
  case True
  thus ?thesis 
    using InCircleS_def assms(2) lt_diff by blast
next
  case False
  hence "P \<noteq> PO"
    by simp
  have "A PO Lt A B \<and> B PO Lt A B" 
    by (metis Diam_def False Lt_cases assms(1) bet__lt1213 bet__lt2313 onc_not_center)
  show ?thesis 
  proof (cases "PO = U")
    case True
    hence "PO = U"
      by simp
    have "PO V Lt PO A" 
    proof (rule cong2_lt__lt [where ?A="PO" and ?B="V" and ?C="PO" and ?D="P"])
      show "PO V Lt PO P" 
        using InCircleS_def assms(3) by auto
      show "Cong PO V PO V" 
        by (simp add: cong_reflexivity)
      show "Cong PO P PO A"  
        using Diam_def OnCircle_def assms(1) not_cong_3412 by blast
    qed
    thus ?thesis 
      by (metis True \<open>A PO Lt A B \<and> B PO Lt A B\<close> lt_right_comm lt_transitivity)
  next
    case False
    hence "PO \<noteq> U" 
      by simp
    obtain V' where "Bet U PO V'" and "Cong PO V' PO V" 
      using segment_construction by blast
    hence "U V Le U V'"
      using not_cong_3412 triangle_inequality by blast
    have "U V' Lt A B"
    proof (rule bet2_lt2__lt [where ?Po="PO" and ?PO="PO"])
      show "Bet U PO V'" 
        by (simp add: \<open>Bet U PO V'\<close>)
      show "Bet A PO B" 
        using Diam_def assms(1) by blast
      show "PO U Lt PO A" 
      proof (rule cong2_lt__lt [where ?A="PO" and ?B="U" and ?C="PO" and ?D="P"])
        show "PO U Lt PO P" 
          using InCircleS_def assms(2) by auto
        show "Cong PO U PO U" 
          by (simp add: cong_reflexivity)
        show "Cong PO P PO A"
          using assms(1) Diam_def OnCircle_def onc_sym by blast
      qed
      show "PO V' Lt PO B"
      proof (rule cong2_lt__lt [where ?A="PO" and ?B="V" and ?C="PO" and ?D="P"])
        show "PO V Lt PO P" 
          using InCircleS_def assms(3) by auto
        show "Cong PO V PO V'" 
          using Cong_cases \<open>Cong PO V' PO V\<close> by blast
        show "Cong PO P PO B"
          using assms(1) Diam_def OnCircle_def onc_sym by blast
      qed
    qed
    then show ?thesis 
      using \<open>U V Le U V'\<close> le1234_lt__lt by blast
  qed
qed

lemma incs_onc_diam__lt: 
  assumes "Diam A B PO P" and
    "U InCircleS PO P" and
    "V OnCircle PO P"
  shows "U V Lt A B" 
proof -
  obtain U' where "Bet V PO U'" and "Cong PO U' PO U" 
    using segment_construction by fastforce
  have "V U' Lt A B" 
  proof (rule bet2_lt_le__lt [where ?Po="PO" and ?PO="PO"])
    show "Bet V PO U'" 
      using \<open>Bet V PO U'\<close> by auto
    show "Bet A PO B" 
      using assms(1) Diam_def by blast
    show "Cong PO V PO A" 
      using Diam_def assms(1) assms(3) onc2__cong by blast
    show "PO U' Lt PO B" 
      by (meson Diam_def InCircleS_def OnCircle_def 
          \<open>Cong PO U' PO U\<close> assms(1) assms(2) cong2_lt__lt not_cong_3412)
  qed
  have "V U Le V U'"
    using \<open>Bet V PO U'\<close> \<open>Cong PO U' PO U\<close> not_cong_3412 triangle_inequality by blast
  thus ?thesis 
    using Lt_cases \<open>V U' Lt A B\<close> le1234_lt__lt by blast
qed

lemma diam_cong_incs__outcs:
  assumes "Diam A B PO P" and
    "Cong A B U V" and
    "U InCircleS PO P" 
  shows "V OutCircleS PO P"
proof (cases "PO = P")
  case True
  then show ?thesis 
    using assms(3) inc112 inc__noutcs_1 incs__outcs by auto
next
  case False
  hence "PO \<noteq> P" 
    by simp
  have "V OnCircle PO P \<or> V InCircleS PO P \<or> V OutCircleS PO P" 
    using circle_cases by blast
  moreover have "V OnCircle PO P \<longrightarrow> V OutCircleS PO P" 
    using assms(1) assms(2) assms(3) cong2_lt__lt cong_reflexivity 
      incs_onc_diam__lt nlt by blast
  moreover
  {
    assume "V InCircleS PO P" 
    hence "U V Lt A B"
      using assms(1) assms(3) incs2_lt_diam by auto
    hence "V OutCircleS PO P" 
      using assms(2) cong__nlt not_cong_3412 by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma diam_uniqueness: 
  assumes "Diam A B PO P" and
    "Cong A X A B" and
    "X OnCircle PO P"
  shows "X = B" 
proof (cases "PO = P")
  case True
  then show ?thesis 
    by (metis Diam_def OnCircle_def assms(1) assms(3) cong_identity_inv)
next
  case False
  hence "PO \<noteq> P"
    by simp
  have "Bet A PO X" 
    by (metis Cong_cases Diam_def assms(1) assms(2) assms(3) bet_col 
        between_trivial2 l4_18 onc2__cong)
  thus ?thesis 
    by (metis Cong_cases Diam_def OnCircle_def assms(1) assms(2)
        between_cong between_trivial2 l5_1)
qed

lemma onc3__ncol:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P"
  shows "\<not> Col A B C"
  using onc2__cong assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
    line_circle_two_points by blast

lemma diam_exists: 
  shows "\<exists> A B. Diam A B PO P \<and> Col A B T" 
  using diam_points Diam_def by blast

lemma chord_intersection:
  assumes "A OnCircle PO P" and
    "B OnCircle PO P" and
    "X OnCircle PO P" and
    "Y OnCircle PO P" and
    "A B TS X Y"
  shows "X Y TS A B" 
proof -
  obtain T where "Col T A B" and "Bet X T Y"
    using TS_def assms(5) by blast
  have "\<not> Col A X Y" 
    using  onc3__ncol[where ?PO="PO" and ?P = "P"] 
      assms(1) assms(3) assms(4) assms(5) ts_distincts by presburger
  moreover have "\<not> Col B X Y"
    using  onc3__ncol[where ?PO="PO" and ?P = "P"] 
    using assms(2) assms(3) assms(4) assms(5) ts_distincts by presburger
  moreover have "Col T X Y" 
    using \<open>Bet X T Y\<close> bet_col col_permutation_4 by blast
  moreover have "Bet A T B"
    using col_inc_onc2__bet \<open>Bet X T Y\<close> \<open>Col T A B\<close> assms(1) assms(2) assms(3) assms(4) 
      assms(5) bet_inc2__inc not_col_permutation_2 onc__inc ts_distincts by blast
  ultimately show ?thesis   
    using TS_def by blast
qed

lemma ray_cut_chord:
  assumes "Diam A B PO P" and
    "X OnCircle PO P" and
    "Y OnCircle PO P" and
    "A B TS X Y" and
    "X Y OS PO A"
  shows "X Y TS PO B" 
proof (rule l9_8_2 [where ?A="A"])
  show "X Y TS A B" 
    using Diam_def assms(1) assms(2) assms(3) assms(4) chord_intersection by blast
  show "X Y OS A PO"
    by (simp add: assms(5) one_side_symmetry)
qed

lemma center_col__diam:
  assumes "A \<noteq> B" and
    "Col PO A B" and
    "A OnCircle PO P" and
    "B OnCircle PO P"
  shows "Diam A B PO P" 
  by (metis Col_def Midpoint_def NCol_cases assms(1) assms(2) assms(3) 
      assms(4) between_cong between_symmetry mid_onc__diam not_cong_3421 onc2__cong)

lemma diam__midpoint: 
  assumes "Diam A B PO P" 
  shows "PO Midpoint A B"
  using Diam_def Midpoint_def 
  by (metis Col_def assms bet_neq21__neq col_onc2__mid l7_3_2)

lemma diam_sym:
  assumes "Diam A B PO P"
  shows "Diam B A PO P" 
  using Diam_def assms between_symmetry by blast

lemma diam_end_uniqueness:
  assumes "Diam A B PO P" and
    "Diam A C PO P"
  shows "B = C" 
  by (meson assms(1) assms(2) diam__midpoint symmetric_point_uniqueness)

lemma center_onc2_mid__ncol:
  assumes (*"PO \<noteq> P" and *)
    "\<not> Col PO A B" and
    (*"A OnCircle PO P" and
"B OnCircle PO P" and*)
    "M Midpoint A B"
  shows "\<not> Col A PO M" 
  by (metis assms(2) assms(1) col_transitivity_2 col_trivial_3 
      midpoint_col midpoint_distinct_1)

lemma bet_chord__diam_or_ncol:
  assumes "A \<noteq> B" and
    "T \<noteq> A" and
    "T \<noteq> B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "Bet A T B" 
  shows "Diam A B PO P \<or> \<not> Col PO A T \<and> \<not> Col PO B T" 
  by (metis Col_def assms(1) assms(2) assms(3) assms(4) assms(5) 
      assms(6) center_col__diam l6_16_1)

lemma mid_chord__diam_or_ncol:
  assumes "A \<noteq> B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "T Midpoint A B"
  shows "Diam A B PO P \<or> \<not>Col PO A T \<and> \<not>Col PO B T" 
  using assms(1) assms(2) assms(3) assms(4) bet_chord__diam_or_ncol 
    midpoint_bet midpoint_distinct_1 by blast

lemma cop_mid_onc2_perp__col:
  assumes "A \<noteq> B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "X Midpoint A B" and
    "X Y Perp A B" and
    "Coplanar PO A B Y"
  shows "Col X Y PO" 
proof (cases "PO = X")
  case True
  thus ?thesis   
    using not_col_distincts by blast
next
  case False
  hence "PO \<noteq> X" 
    by simp
  show ?thesis
  proof (rule cop_perp2__col [where ?A ="A" and ?B="B"])
    show "Coplanar A B Y PO" 
      by (simp add: assms(6) coplanar_perm_9)
    show "X Y Perp A B" 
      by (simp add: assms(5))
    show "X PO Perp A B"
      using False assms(1) assms(2) assms(3) assms(4) mid_onc2__perp 
        perp_left_comm by presburger
  qed
qed

lemma cong2_cop2_onc3__eq:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and 
    "B \<noteq> C" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "Coplanar A B C PO" and
    "Cong X A X B" and
    "Cong X A X C" and
    "Coplanar A B C X"
  shows "X = PO" 
  by (meson assms(1) assms(10) assms(2) assms(3) assms(4) assms(5) 
      assms(6) assms(7) assms(8) assms(9) cong4_cop2__eq not_cong_2143 onc2__cong)

lemma tree_points_onc_cop:
  assumes "PO \<noteq> P"
  shows "\<exists> A B C. A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> 
                  A OnCircle PO P \<and> B OnCircle PO P \<and> C OnCircle PO P \<and> 
                  Coplanar A B C PO" 
proof -
  obtain X where "\<not> Col PO P X"
    using assms not_col_exists by presburger
  obtain B C where "Bet B PO C" and "Col B C X" and "B OnCircle PO P" and "C OnCircle PO P" 
    using diam_points by force
  have "P \<noteq> B" 
    by (metis Col_def \<open>Bet B PO C\<close> \<open>Col B C X\<close> \<open>\<not> Col PO P X\<close> 
        bet_neq21__neq col3 not_col_distincts)
  moreover have "P \<noteq> C" 
    by (metis Out_def \<open>Bet B PO C\<close> \<open>Col B C X\<close> \<open>\<not> Col PO P X\<close> calculation col3 
        not_col_distincts out_col)
  moreover have "B \<noteq> C" 
    using \<open>B OnCircle PO P\<close> \<open>Bet B PO C\<close> assms between_identity onc_not_center by blast
  moreover have "P OnCircle PO P" 
    using onc212 by auto
  moreover have "Coplanar P B C PO" 
    by (metis Bet_cases Col_def \<open>Bet B PO C\<close> ncop__ncols)
  ultimately show ?thesis 
    using \<open>B OnCircle PO P\<close> \<open>C OnCircle PO P\<close> by blast
qed

lemma tree_points_onc_cop2:
  assumes "PO \<noteq> P"
  shows "\<exists> A B C. A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> 
                A OnCircle PO P \<and> B OnCircle PO P \<and> C OnCircle PO P \<and>
                Coplanar A B C PO \<and> Coplanar A B C Q" 
proof (cases "PO = Q")
  case True
  then show ?thesis   
    using assms tree_points_onc_cop by auto
next
  case False
  hence "PO \<noteq> Q"
    by simp
  then obtain X where "\<not> Col PO Q X" 
    using not_col_exists by blast
  obtain B C where "Bet B PO C" and "Col B C X" and "B OnCircle PO P" and "C OnCircle PO P" 
    using diam_points by force
  obtain A where "PO Out A Q" and "Cong PO A PO P" 
    using \<open>PO \<noteq> Q\<close> assms l6_11_existence by metis
  have "A \<noteq> B" 
    by (metis Col_def \<open>Bet B PO C\<close> \<open>Col B C X\<close> \<open>PO Out A Q\<close> \<open>\<not> Col PO Q X\<close> 
        bet_out__bet between_equality between_trivial between_trivial2 colx out_col)
  moreover have "A \<noteq> C" 
    by (metis Bet_perm False \<open>Bet B PO C\<close> \<open>Col B C X\<close> \<open>PO Out A Q\<close> 
        \<open>\<not> Col PO Q X\<close> bet_out_1 bet_out__bet calculation colx 
        not_col_permutation_4 not_col_permutation_5 out_col)
  moreover have "B \<noteq> C" 
    using \<open>B OnCircle PO P\<close> \<open>Bet B PO C\<close> assms bet_neq12__neq onc_not_center by blast
  moreover have "A OnCircle PO P" 
    by (simp add: OnCircle_def \<open>Cong PO A PO P\<close>)
  moreover have "Coplanar A B C PO" 
    using \<open>Bet B PO C\<close> bet__coplanar coplanar_perm_19 by blast
  moreover hence "Coplanar A B C Q" 
    by (metis Out_def \<open>PO Out A Q\<close> col_cop__cop coplanar_perm_8 not_col_permutation_4 out_col)
  ultimately show ?thesis 
    using \<open>B OnCircle PO P\<close> \<open>C OnCircle PO P\<close> by blast
qed


lemma tree_points_onc:
  assumes "PO \<noteq> P"
  shows "\<exists> A B C.
  A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> A OnCircle PO P \<and> B OnCircle PO P \<and> C OnCircle PO P"
proof -
  obtain A B C where "A \<noteq> B" and "A \<noteq> C" and "B \<noteq> C" and 
    "A OnCircle PO P" and "B OnCircle PO P" and "C OnCircle PO P" and
    "Coplanar A B C PO" 
    using assms tree_points_onc_cop by force
  thus ?thesis 
    by blast
qed

lemma bet_cop_onc2__ex_onc_os_out:
  assumes "A \<noteq> I" and 
    "B \<noteq> I" and 
    "\<not> Col A B C" and
    "\<not> Col A B PO" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "Bet A I B" and
    "Coplanar A B C PO"
  shows "\<exists> C1. C1 Out PO I \<and> C1 OnCircle PO P \<and> A B OS C C1" 
proof -
  obtain C1 C2 where "Bet C1 PO C2" and "Col C1 C2 I" and 
    "C1 OnCircle PO P" and "C2 OnCircle PO P" 
    using diam_points by blast
  have "A B TS C1 C2" 
  proof (rule chord_intersection [where ?PO="PO" and ?P="P"])
    show "C1 OnCircle PO P" 
      using \<open>C1 OnCircle PO P\<close> by auto
    show "C2 OnCircle PO P" 
      by (simp add: \<open>C2 OnCircle PO P\<close>)
    show "A OnCircle PO P" 
      by (simp add: assms(5))
    show "B OnCircle PO P" 
      by (simp add: assms(6))
    have "C1 \<noteq> C2" 
      by (metis \<open>Bet C1 PO C2\<close> \<open>C1 OnCircle PO P\<close> assms(4) assms(5) 
          bet_neq12__neq col_trivial_3 onc_not_center onc_sym)
    show "C1 C2 TS A B"
    proof -
      {
        assume "Col A C1 C2" 
        hence "Col A B PO" 
          by (metis \<open>Bet C1 PO C2\<close> \<open>C1 \<noteq> C2\<close> \<open>Col C1 C2 I\<close> assms(1)
              assms(7) bet_col1 between_trivial col_transitivity_1 
              not_col_permutation_3 not_col_permutation_5)
        hence False 
          by (simp add: assms(4))
      }
      moreover 
      {
        assume "Col B C1 C2" 
        hence "Col A B PO" 
          by (metis \<open>Col C1 C2 I\<close> assms(2) assms(7) bet_col bet_col1 
              calculation col_permutation_1 l6_21)
        hence False 
          by (simp add: assms(4))
      }
      moreover have "Col I C1 C2" 
        using NCol_cases \<open>Col C1 C2 I\<close> by blast
      moreover have "Bet A I B" 
        by (simp add: assms(7))
      ultimately show ?thesis
        using TS_def by blast
    qed
  qed
  have "Bet C1 I C2" 
    by (meson NCol_cases \<open>A B TS C1 C2\<close> \<open>Col C1 C2 I\<close> assms(7) bet_col l9_18)
  have "\<not> Col C1 A B" 
    using TS_def \<open>A B TS C1 C2\<close> by auto
  have "Coplanar A B C C1"
  proof (rule coplanar_trans_1 [where ?P="PO"])
    show "\<not> Col PO A B" 
      by (simp add: assms(4) not_col_permutation_2)
    show "Coplanar PO A B C" 
      using assms(8) coplanar_perm_18 by blast
    show "Coplanar PO A B C1"
      using \<open>A B TS C1 C2\<close> \<open>Bet C1 PO C2\<close> bet_cop__cop coplanar_perm_18 ts__coplanar by blast
  qed
  hence "A B TS C C1 \<or> A B OS C C1"  
    using cop__one_or_two_sides Col_cases \<open>\<not> Col C1 A B\<close> assms(3) by blast
  moreover
  {
    assume "A B TS C C1"
    have "C2 Out PO I" 
      by (metis Bet_cases Col_def OnCircle_def Out_cases TS_def 
          \<open>A B TS C1 C2\<close> \<open>Bet C1 I C2\<close> \<open>Bet C1 PO C2\<close> \<open>C2 OnCircle PO P\<close> 
          assms(6) assms(7) bet_out_1 between_trivial2 cong_reverse_identity 
          l6_7 not_cong_3421)
    moreover have "A B OS C C2" 
      using OS_def \<open>A B TS C C1\<close> \<open>A B TS C1 C2\<close> l9_2 by blast
    ultimately have "C2 Out PO I \<and> C2 OnCircle PO P \<and> A B OS C C2" 
      using \<open>C2 OnCircle PO P\<close> by blast
  }
  moreover 
  {
    assume "A B OS C C1"
    have "C1 Out PO I" 
      by (metis Col_def \<open>A B TS C1 C2\<close> \<open>Bet C1 I C2\<close> 
          \<open>Bet C1 PO C2\<close> \<open>C1 OnCircle PO P\<close> \<open>C2 OnCircle PO P\<close> 
          \<open>\<not> Col C1 A B\<close> assms(7) bet2__out between_symmetry l9_9 
          onc_not_center onc_sym one_side_reflexivity)
    hence "C1 Out PO I \<and> C1 OnCircle PO P \<and> A B OS C C1" 
      using \<open>C1 OnCircle PO P\<close> \<open>A B OS C C1\<close>
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma eqc_chara_1: 
  assumes "EqC A B C D" 
  shows "A = C \<and> Cong A B C D" 
proof -
  have "A = C"
  proof (cases "A = B")
    case True
    thus ?thesis 
      by (metis EqC_def OnCircle_def assms cong_identity_inv onc212 tree_points_onc)
  next
    case False
    hence "A \<noteq> B" 
      by simp
    then obtain B0 B1 B2 where "B0 \<noteq> B1" and "B0 \<noteq> B2" and "B1 \<noteq> B2" and
      "B0 OnCircle A B" and "B1 OnCircle A B" and "B2 OnCircle A B" and
      "Coplanar B0 B1 B2 A" and "Coplanar B0 B1 B2 C" 
      using tree_points_onc_cop2 by blast
    thus ?thesis 
      by (meson EqC_def assms cong2_cop2_onc3__eq onc2__cong) 
  qed
  moreover have "Cong A B C D" 
    using EqC_def OnCircle_def assms calculation onc212 by blast
  ultimately show ?thesis 
    by blast
qed

lemma eqc_chara_2: 
  assumes "A = C" and
    "Cong A B C D"
  shows "EqC A B C D" 
  by (metis Cong_cases EqC_def OnCircle_def assms(1) assms(2) onc2__cong)

(** Two circles are equal if and only if they have the same center and the same radius *)

lemma eqc_chara: 
  shows "EqC A B C D \<longleftrightarrow> (A = C \<and> Cong A B C D)" 
  using eqc_chara_1 eqc_chara_2 by blast

lemma neqc_chara_1:
  assumes "A \<noteq> B" and
    "\<not> EqC A B C D" 
  shows "\<exists> X. X OnCircle A B \<and> \<not> X OnCircle C D" 
proof (cases "A = C")
  case True
  thus ?thesis   
    by (metis OnCircle_def assms(2) eqc_chara_2 onc212)
next
  case False
  hence "A \<noteq> C"
    by simp
  obtain B0 B1 B2 where "B0 \<noteq> B1" and "B0 \<noteq> B2" and "B1 \<noteq> B2" and
    "B0 OnCircle A B" and "B1 OnCircle A B" and "B2 OnCircle A B" and
    "Coplanar B0 B1 B2 A" and "Coplanar B0 B1 B2 C" 
    using tree_points_onc_cop2 assms(1) by blast
  show ?thesis
  proof (cases "Cong C B0 C D")
    case True
    thus ?thesis 
      by (meson False \<open>B0 OnCircle A B\<close> \<open>B0 \<noteq> B1\<close> \<open>B0 \<noteq> B2\<close> 
          \<open>B1 OnCircle A B\<close> \<open>B1 \<noteq> B2\<close> \<open>B2 OnCircle A B\<close> \<open>Coplanar B0 B1 B2 A\<close> 
          \<open>Coplanar B0 B1 B2 C\<close> cong2_cop2_onc3__eq onc2__cong)
  next
    case False
    hence "\<not> Cong C B0 C D"
      by simp
    show ?thesis 
    proof (cases "Cong C B1 C D")
      case True
      then show ?thesis 
        using False OnCircle_def \<open>B0 OnCircle A B\<close> by blast
    next
      case False
      hence "\<not> Cong C B1 C D" 
        by simp
      show ?thesis 
      proof (cases "Cong C B2 C D")
        case True
        then show ?thesis 
          using False OnCircle_def \<open>B1 OnCircle A B\<close> by blast
      next
        case False
        hence "\<not> Cong C B2 C D"
          by simp
        then show ?thesis 
          using OnCircle_def \<open>B2 OnCircle A B\<close> by blast
      qed
    qed
  qed
qed

lemma neqc_chara_2:
  assumes (*"A \<noteq> B" and*)
    "X OnCircle A B" and
    "\<not> X OnCircle C D"
  shows "\<not> EqC A B C D" 
  using EqC_def assms(2) assms(1) by blast

(** Two circles are distinct if and only if there is a point
    belonging to the first and not to the second *)

lemma neqc_chara:
  assumes "A \<noteq> B" 
  shows "\<not> EqC A B C D \<longleftrightarrow> (\<exists> X. X OnCircle A B \<and> \<not> X OnCircle C D)" 
  using assms neqc_chara_1 neqc_chara_2 by blast

(** The EqC predicate is an equivalence relation on ordered pairs of points *)

lemma eqc_refl: 
  shows "EqC A B A B" 
  by (simp add: EqC_def)

lemma eqc_sym: 
  assumes "EqC A B C D"
  shows "EqC C D A B" 
  using EqC_def assms by auto

lemma eqc_trans: 
  assumes "EqC A B C D" and
    "EqC C D E F"
  shows "EqC A B E F" 
  by (metis OnCircle_def assms(1) assms(2) eqc_chara not_cong_3412 onc2__cong)

(** If two circles have three common points, then they are equal *)

lemma cop2_onc6__eqc: 
  assumes "A \<noteq> B" and 
    "B \<noteq> C" and
    "A \<noteq> C" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "Coplanar A B C PO" and
    "A OnCircle O' P'" and
    "B OnCircle O' P'" and
    "C OnCircle O' P'" and
    "Coplanar A B C O'"
  shows "EqC PO P O' P'" 
proof -
  have "PO = O'"
    by (meson assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) 
        assms(5) assms(6) assms(7) assms(8) assms(9) 
        cong2_cop2_onc3__eq onc2__cong)
  thus ?thesis 
    by (metis OnCircle_def assms(10) assms(6) eqc_chara_2 onc212 onc2__cong)
qed

(** If four coplanar points belong to a same sphere, then they belong to a same circle.
    This lemma justifies our definition of Concyclic. *)

lemma concyclic_aux:
  assumes "Concyclic A B C D" 
  shows "\<exists> PO P. A OnCircle PO P \<and> B OnCircle PO P \<and> C OnCircle PO P \<and> 
D OnCircle PO P \<and> Coplanar A B C PO" 
proof-
  have 1: "Coplanar A B C D \<and>
  (\<exists> O1 P1. A OnCircle O1 P1 \<and> B OnCircle O1 P1 \<and> C OnCircle O1 P1 \<and> D OnCircle O1 P1)" 
    using Concyclic_def assms by blast
  then obtain O1 P1 where "A OnCircle O1 P1" and "B OnCircle O1 P1" and
    "C OnCircle O1 P1" and "D OnCircle O1 P1" 
    by blast
  have "Coplanar A B C D" 
    using 1 by blast
  show ?thesis
  proof (cases "Col A B C")
    case True
    then show ?thesis 
      using \<open>A OnCircle O1 P1\<close> \<open>B OnCircle O1 P1\<close> \<open>C OnCircle O1 P1\<close> 
        \<open>D OnCircle O1 P1\<close> col__coplanar by blast
  next
    case False
    hence "\<not> Col A B C" 
      by simp
    obtain PO where "Coplanar A B C PO" and "\<forall> E. Coplanar A B C E \<longrightarrow> Per E PO O1"
      using l11_62_existence by blast
    have "\<forall> A B. (A OnCircle O1 P1 \<and> B OnCircle O1 P1) \<longrightarrow> Cong O1 A O1 B" 
      using onc2__cong by blast
    have "A OnCircle PO A" 
      by (simp add: onc212)
    moreover have "Cong PO B PO A" 
    proof (rule cong2_per2__cong [where ?C="O1" and ?C'="O1"], insert \<open>Coplanar A B C PO\<close>)
      show "Per B PO O1" 
        using \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E PO O1\<close> ncop_distincts by blast 
      show "Per A PO O1"   
        using \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E PO O1\<close> ncop_distincts by blast 
      show "Cong B O1 A O1"       
        using \<open>A OnCircle O1 P1\<close> \<open>B OnCircle O1 P1\<close> cong_4321 onc2__cong by blast
      show "Cong PO O1 PO O1" 
        by (simp add: cong_reflexivity)
    qed
    hence "B OnCircle PO A" 
      by (simp add: OnCircle_def)
    moreover have "Cong PO C PO A" 
    proof (rule cong2_per2__cong [where ?C="O1" and ?C'="O1"])
      show "Per C PO O1" 
        using \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E PO O1\<close> ncop_distincts by blast
      show "Per A PO O1"  
        using \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E PO O1\<close> ncop_distincts by blast
      show "Cong C O1 A O1"  
        using \<open>A OnCircle O1 P1\<close> \<open>C OnCircle O1 P1\<close> cong_4321 onc2__cong by blast
      show "Cong PO O1 PO O1"  
        by (simp add: cong_reflexivity)
    qed
    hence "C OnCircle PO A" 
      by (simp add: OnCircle_def)
    moreover have "Cong PO D PO A" 
    proof (rule cong2_per2__cong [where ?C="O1" and ?C'="O1"])
      show "Per D PO O1" 
        using Concyclic_def \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E PO O1\<close> assms by blast
      show "Per A PO O1" 
        using \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E PO O1\<close> ncop_distincts by blast
      show "Cong D O1 A O1" 
        using \<open>A OnCircle O1 P1\<close> \<open>D OnCircle O1 P1\<close> 
          \<open>\<forall>A B. A OnCircle O1 P1 \<and> B OnCircle O1 P1 \<longrightarrow> Cong O1 A O1 B\<close> 
          not_cong_4321 by blast
      show "Cong PO O1 PO O1" 
        using cong_reflexivity by auto
    qed
    hence "D OnCircle PO A"   
      by (simp add: OnCircle_def)
    ultimately show ?thesis 
      using \<open>Coplanar A B C PO\<close> by blast
  qed
qed

lemma concyclic_perm_1:
  assumes "Concyclic A B C D" 
  shows "Concyclic B C D A" 
  using Concyclic_def assms coplanar_perm_9 by blast

lemma concyclic_gen_perm_1:
  assumes "ConcyclicGen A B C D"
  shows "ConcyclicGen B C D A" 
  by (metis Col_cases ConcyclicGen_def assms concyclic_perm_1)

lemma concyclic_perm_2: 
  assumes "Concyclic A B C D" 
  shows "Concyclic B A C D" 
  by (meson Concyclic_def assms concyclic_perm_1 coplanar_perm_20)

lemma concyclic_gen_perm_2:
  assumes "ConcyclicGen A B C D" 
  shows "ConcyclicGen B A C D" 
  using ConcyclicGen_def assms concyclic_perm_2 not_col_permutation_4 by blast

lemma concyclic_trans_1:
  assumes "\<not> Col P Q R" and
    "Concyclic P Q R A" and 
    "Concyclic P Q R B" 
  shows "Concyclic Q R A B" 
proof (simp add: Concyclic_def,rule conjI)
  show "Coplanar Q R A B" 
    using Concyclic_def assms(1) assms(2) assms(3) coplanar_trans_1 by presburger
  show "\<exists>PO P. Q OnCircle PO P  \<and> R OnCircle PO P  \<and> A OnCircle PO P  \<and> B OnCircle PO P" 
  proof -
    obtain PO M where "P OnCircle PO M" and "Q OnCircle PO M" and "R OnCircle PO M" and 
      "A OnCircle PO M" and "Coplanar P Q R PO"
      using concyclic_aux assms(2) by blast
    obtain O' M' where "P OnCircle O' M'" and "Q OnCircle O' M'" and "R OnCircle O' M'" and 
      "B OnCircle O' M'" and "Coplanar P Q R O'"
      using concyclic_aux assms(3) by blast
    have "B OnCircle PO M"       
      using cop2_onc6__eqc \<open>B OnCircle O' M'\<close> \<open>Coplanar P Q R O'\<close> 
        \<open>Coplanar P Q R PO\<close> \<open>P OnCircle O' M'\<close> \<open>P OnCircle PO M\<close> 
        \<open>Q OnCircle O' M'\<close> \<open>Q OnCircle PO M\<close> \<open>R OnCircle O' M'\<close>
        \<open>R OnCircle PO M\<close> assms(1) neqc_chara_2 not_col_distincts by blast
    thus ?thesis
      using \<open>A OnCircle PO M\<close> \<open>Q OnCircle PO M\<close> \<open>R OnCircle PO M\<close> by blast
  qed
qed

lemma concyclic_gen_trans_1:
  assumes "\<not> Col P Q R" and
    "ConcyclicGen P Q R A" and 
    "ConcyclicGen P Q R B"
  shows "ConcyclicGen Q R A B" 
  using ConcyclicGen_def assms(1) assms(2) assms(3) concyclic_trans_1 by presburger

lemma concyclic_pseudo_trans: 
  assumes "\<not> Col P Q R" and
    "Concyclic P Q R A" and 
    "Concyclic P Q R B" and
    "Concyclic P Q R C" and
    "Concyclic P Q R D" 
  shows "Concyclic A B C D" 
proof (simp add: Concyclic_def,rule conjI)
  show "Coplanar A B C D"  
  proof -
    have "Coplanar P Q R A"   
      using Concyclic_def assms(2) by blast
    moreover have "Coplanar P Q R B"          
      using Concyclic_def assms(3) by blast
    moreover have "Coplanar P Q R C"       
      using Concyclic_def assms(4) by blast
    moreover have "Coplanar P Q R D"       
      using Concyclic_def assms(5) by blast
    ultimately show ?thesis 
      using assms(1) coplanar_pseudo_trans by blast
  qed
  show "\<exists> PO P. A OnCircle PO P  \<and> B OnCircle PO P  \<and> C OnCircle PO P  \<and> D OnCircle PO P"
  proof -
    obtain OA MA where "P OnCircle OA MA" and "Q OnCircle OA MA" and "R OnCircle OA MA" and 
      "A OnCircle OA MA" and "Coplanar P Q R OA"
      using concyclic_aux assms(2) by blast
    obtain OB MB where "P OnCircle OB MB" and "Q OnCircle OB MB" and "R OnCircle OB MB" and 
      "B OnCircle OB MB" and "Coplanar P Q R OB"
      using concyclic_aux assms(3) by blast
    obtain OC MC where "P OnCircle OC MC" and "Q OnCircle OC MC" and "R OnCircle OC MC" and 
      "C OnCircle OC MC" and "Coplanar P Q R OC"
      using concyclic_aux assms(4) by blast
    obtain OD MD where "P OnCircle OD MD" and "Q OnCircle OD MD" and "R OnCircle OD MD" and 
      "D OnCircle OD MD" and "Coplanar P Q R OD"
      using concyclic_aux assms(5) by blast
    have "A OnCircle OA MA" 
      by (simp add: \<open>A OnCircle OA MA\<close>)
    moreover have "B OnCircle OA P" 
      using OnCircle_def \<open>B OnCircle OB MB\<close> \<open>Coplanar P Q R OA\<close> \<open>Coplanar P Q R OB\<close> 
        \<open>P OnCircle OA MA\<close> \<open>P OnCircle OB MB\<close> \<open>Q OnCircle OA MA\<close> 
        \<open>Q OnCircle OB MB\<close> \<open>R OnCircle OA MA\<close> \<open>R OnCircle OB MB\<close> 
        assms(1) cong2_cop2_onc3__eq not_col_distincts onc2__cong by blast
    moreover have "C OnCircle OA P" 
      using OnCircle_def \<open>C OnCircle OC MC\<close> \<open>Coplanar P Q R OA\<close> \<open>Coplanar P Q R OC\<close> 
        \<open>P OnCircle OA MA\<close> \<open>P OnCircle OC MC\<close> \<open>Q OnCircle OA MA\<close> 
        \<open>Q OnCircle OC MC\<close> \<open>R OnCircle OA MA\<close> \<open>R OnCircle OC MC\<close> 
        assms(1) cong2_cop2_onc3__eq not_col_distincts onc2__cong by blast
    moreover have "D OnCircle OA P" 
      using OnCircle_def \<open>Coplanar P Q R OA\<close> \<open>Coplanar P Q R OD\<close> \<open>D OnCircle OD MD\<close> 
        \<open>P OnCircle OA MA\<close> \<open>P OnCircle OD MD\<close> \<open>Q OnCircle OA MA\<close> 
        \<open>Q OnCircle OD MD\<close> \<open>R OnCircle OA MA\<close> \<open>R OnCircle OD MD\<close> 
        assms(1) cong2_cop2_onc3__eq not_col_distincts onc2__cong by blast
    ultimately show ?thesis 
      using OnCircle_def \<open>P OnCircle OA MA\<close> onc2__cong by blast
  qed
qed

lemma concyclic_gen_pseudo_trans:
  assumes "\<not> Col P Q R" and
    "ConcyclicGen P Q R A"
    "ConcyclicGen P Q R B"
    "ConcyclicGen P Q R C"
    "ConcyclicGen P Q R D"
  shows "ConcyclicGen A B C D" 
  using ConcyclicGen_def assms(1) assms(2) assms(3) assms(4) assms(5) 
    concyclic_pseudo_trans by presburger

end

subsection "Axioms continuity"

context Tarski_neutral_dimensionless

begin

subsubsection "Continuity Defs"

(** GeoCoq: continuity_axioms.v In this file, we introduce elementary continuity properties.
    These properties are different variant to assert that the intersection
    of line, segment and circles exists under some assumptions.
    Adding one of these properties as axiom to the Tarski_2D type class gives us
    a definition of ruler and compass geometry.
    The links between these properties are in file elementary_continuity_props.v .

    We also introduce other continuity properties.
*)


(** If there is a point P inside a circle, and Q outside then there is
    a point Z of the segment PQ which is on the circle. *)

definition segment_circle :: bool
  ("SegmentCircle" 50)
  where
    "segment_circle \<equiv> \<forall> A B P Q. (P InCircle A B \<and> Q OutCircle A B) \<longrightarrow>
  (\<exists> Z. Bet P Z Q \<and> Z OnCircle A B)"

(** Given a line UV which contains a point inside the circle, there is
   a point of line UV which is on the circle. *)

definition one_point_line_circle :: bool
  ("OnePointLineCircle" 50)
  where
    "one_point_line_circle \<equiv> \<forall> A B U V P.
  Col U V P \<and> U \<noteq> V \<and> Bet A P B \<longrightarrow> (\<exists> Z. Col U V Z \<and> Z OnCircle A B)"

(** Given a line UV which contains a point P inside the circle, there are
  two points on line UV which belong to the circle and they are distinct if
 if P is strictly inside the circle. *)

definition two_points_line_circle :: bool
  ("TwoPointLineCircle" 50)
  where
    "TwoPointLineCircle \<equiv> \<forall> A B U V P.
  (Col U V P \<and> U \<noteq> V \<and> Bet A P B) \<longrightarrow> (\<exists> Z1 Z2. Col U V Z1 \<and> Z1 OnCircle A B \<and>
                Col U V Z2 \<and> Z2 OnCircle A B \<and>
                Bet Z1 P Z2 \<and> (P \<noteq> B \<longrightarrow> Z1 \<noteq> Z2))"

(** Given two circles (A,B) and (C,D), if there are two points of (C,D)
 one inside and one outside (A,B) then there is a point of intersection
 of the two circles. *)

definition circle_circle :: bool
  ("CircleCircle" 50)
  where
    "circle_circle \<equiv> \<forall> A B C D P Q.
  (P OnCircle C D  \<and> Q OnCircle C D \<and> P InCircle A B \<and> Q OutCircle A B) 
\<longrightarrow> (\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D)"

(** Given two circles (A,B) and (C,D),
   if there is a point of (A,B) which is inside (C,D)
  and vice-versa, then there is a point of intersection of the two circles. *)

definition circle_circle_bis :: bool
  ("CircleCircleBis" 50)
  where
    "circle_circle_bis \<equiv> \<forall> A B C D P Q.
(P OnCircle C D \<and> P InCircle A B \<and> Q OnCircle A B \<and> Q InCircle C D)
\<longrightarrow> (\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D)"

(** A simplification of the previous statement we use in our axiom system. *)

definition circle_circle_axiom :: bool
  ("CircleCircleAxiom" 50)
  where
    "circle_circle_axiom \<equiv> \<forall> A B C D B' D'.
(Cong A B' A B \<and> Cong C D' C D \<and> Bet A D' B \<and> Bet C B' D)
\<longrightarrow> (\<exists> Z. Cong A Z A B \<and> Cong C Z C D)"

(** Given two circles (A,B) and (C,D), if there are two points of (C,D)
 one inside and one outside (A,B) then there are two points of intersection
 of the two circles.
 They are distinct if the inside and outside properties are strict. *)

definition circle_circle_two :: bool
  ("CircleCircleTwo" 50)
  where
    "circle_circle_two \<equiv> \<forall> A B C D P Q.
(P OnCircle C D \<and> Q OnCircle C D \<and> P InCircle A B \<and> Q OutCircle A B)
\<longrightarrow> (\<exists> Z1 Z2. Z1 OnCircle A B \<and> Z1 OnCircle C D \<and>
    Z2 OnCircle A B \<and> Z2 OnCircle  C D \<and>
    ((P InCircleS A B \<and> Q OutCircleS A B) \<longrightarrow> Z1 \<noteq> Z2))"

(** Proposition 22 from Euclid's Elements, Book I:
 "Out of three straight lines, which are equal to three given straight lines, 
  to construct a triangle:
 thus it is necessary that two of the straight lines taken together in any manner
 should be greater than the remaining one."
*)

definition euclid_s_prop_1_22 :: bool
  ("EuclidsProp122" 50)
  where
    "euclid_s_prop_1_22 \<equiv> \<forall> A B C D E F A' B' C' D' E' F'.
(A B C D SumS E' F' \<and> A B E F SumS C' D' \<and> C D E F SumS A' B' \<and>
  E F Le E' F' \<and> C D Le C' D' \<and> A B Le A' B') \<longrightarrow>
(\<exists> P Q R. Cong P Q A B \<and> Cong P R C D \<and> Cong Q R E F)"

(*
Definition weak_cantor_s_axiom := forall (A B:nat -> Tpoint),
  (forall n, Bet (A n) (A (S n)) (B (S n)) \<and> Bet (A (S n)) (B (S n)) (B n) \<and> A (S n) \<noteq> B (S n)) ->
  exists X, forall n, Bet (A n) X (B n).
*)

(** Nested A B describes the fact that the sequences A and B form the end points
 of nested non-degenerate segments *)


definition Nested ::
  "[(nat \<Rightarrow> TPoint \<Rightarrow> bool),(nat \<Rightarrow>TPoint\<Rightarrow> bool)] \<Rightarrow> bool"
  ("Nested _ _" [99,99] 50)
  where
    "Nested A B \<equiv>
 (\<forall> n. (\<exists> An Bn. A n An \<and> B n Bn)) \<and>
 (\<forall> n An Am Bm Bn.
    (A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn) 
\<longrightarrow>
(Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm))"

definition CantorsAxiom :: bool
  ("CantorsAxiom" 50)
  where
    "CantorsAxiom \<equiv> \<forall> A B. Nested A B \<longrightarrow>
 (\<exists> X. \<forall> n An Bn. (A n An \<and> B n Bn) \<longrightarrow> Bet An X Bn)"

definition DedekindsAxiom :: bool
  ("DedekindsAxiom" 50)
  where
    "DedekindsAxiom \<equiv> \<forall> Alpha Beta.
  (\<exists> A. \<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet A X Y) \<longrightarrow>
  (\<exists> B. \<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet X B Y)"

definition DedekindVariant :: bool
  ("DedekindVariant" 50)
  where
    "DedekindVariant \<equiv> \<forall> Alpha Beta :: TPoint \<Rightarrow> bool. \<forall> A C.
(Alpha A \<and> Beta C \<and>
 (\<forall> P. A Out P C \<longrightarrow> (Alpha P \<or> Beta P)) \<and>
 (\<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> (Bet A X Y \<and> X \<noteq> Y)))
\<longrightarrow>
  (\<exists> B. \<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet X B Y)"

subsubsection "Dedekind Variant"

lemma dedekind_equiv_R1: 
  assumes "DedekindsAxiom"
  shows "DedekindVariant" 
  using DedekindsAxiom_def DedekindVariant_def assms by metis

definition Alpha'Fun :: "TPoint \<Rightarrow> (TPoint \<Rightarrow> bool) \<Rightarrow> (TPoint \<Rightarrow> bool)"
  where
    "Alpha'Fun A Alpha \<equiv> \<lambda> X'::TPoint. X' = A \<or> (\<exists> X::TPoint. Alpha X \<and> Bet A X' X)"

definition Beta'Fun :: "TPoint \<Rightarrow> TPoint \<Rightarrow> (TPoint \<Rightarrow> bool) \<Rightarrow> (TPoint \<Rightarrow> bool)"
  where
    "Beta'Fun A C Alpha \<equiv> \<lambda> Y'::TPoint. A Out Y' C \<and> \<not> (\<exists> X::TPoint. Alpha X \<and> Bet A Y' X)"

lemma dedekind_equiv_R2:
  assumes "DedekindVariant" 
  shows "DedekindsAxiom" 
proof -
  {
    fix Alpha Beta :: "TPoint \<Rightarrow> bool"
    assume "\<exists> A.(\<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet A X Y)" 
    then obtain A where "\<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet A X Y" 
      by blast
    have "(\<exists> B. \<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet X B Y)"
    proof (cases "Beta A")
      case True
      thus ?thesis 
        using \<open>\<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> Bet A X Y\<close> between_identity by blast
    next
      case False
      hence "\<not> Beta A" 
        by simp
      show ?thesis 
      proof (cases "\<exists> C. Beta C")
        case True
        then obtain C where "Beta C"
          by auto
        show ?thesis 
        proof (cases "\<exists> P. Alpha P \<and> Beta P")
          case True
          thus ?thesis 
            by (meson \<open>\<exists>A. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> Bet A X Y\<close> between_exchange3)
        next
          case False
          hence "\<not> (\<exists> P. Alpha P \<and> Beta P)"
            by fast
          show ?thesis 
          proof (cases "\<exists> X. Alpha X \<and> X \<noteq> A")
            case True
            hence "\<exists> X. Alpha X \<and> X \<noteq> A"
              by simp
            have "\<exists> B. \<forall> X Y. Alpha'Fun A Alpha X \<and> Beta'Fun A C Alpha Y \<longrightarrow>Bet X B Y" 
            proof -
              have "A = A \<or> (\<exists> X::TPoint. Alpha X \<and> Bet A A X)" 
                by blast
              hence "Alpha'Fun A Alpha A" 
                using Alpha'Fun_def by force
              moreover
              have "A Out C C \<and> \<not> (\<exists> X::TPoint. Alpha X \<and> Bet A C X)" 
                by (metis False \<open>Beta C\<close> \<open>\<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> Bet A X Y\<close> \<open>\<not> Beta A\<close> 
                    between_equality_2 out_trivial)
              hence "Beta'Fun A C Alpha C" 
                using Beta'Fun_def by simp
              moreover 
              {
                fix P
                assume "A Out P C"
                have "(P = A \<or> (\<exists> X::TPoint. Alpha X \<and> Bet A P X)) \<or> 
                      (A Out P C \<and> \<not> (\<exists> X::TPoint. Alpha X \<and> Bet A P X))" 
                  using \<open>A Out P C\<close> by fastforce
                hence "Alpha'Fun A Alpha P \<or> Beta'Fun A C Alpha P" 
                  using Alpha'Fun_def Beta'Fun_def by simp
              }
              hence "\<forall> P. A Out P C \<longrightarrow> (Alpha'Fun A Alpha P \<or> Beta'Fun A C Alpha P)" by blast
              moreover {
                fix X' Y'
                assume "Alpha'Fun A Alpha X'" and "Beta'Fun A C Alpha Y'" 
                hence "X' = A \<or> (\<exists> X::TPoint. Alpha X \<and> Bet A X' X)" 
                  using Alpha'Fun_def by simp
                have "A Out Y' C \<and> \<not> (\<exists> X::TPoint. Alpha X \<and> Bet A Y' X)" 
                  using Beta'Fun_def \<open>Beta'Fun A C Alpha Y'\<close> by presburger
                have "Bet A X' Y' \<and> X' \<noteq> Y'" 
                proof (cases "X' = A")
                  case True
                  thus ?thesis 
                    using \<open>A Out Y' C \<and> (\<nexists>X. Alpha X \<and> Bet A Y' X)\<close> 
                      \<open>\<exists>X. Alpha X \<and> X \<noteq> A\<close> between_trivial2 by blast
                next
                  case False
                  hence "X' \<noteq> A"
                    by simp
                  then obtain X where "Alpha X" and "Bet A X' X" 
                    using \<open>X' = A \<or> (\<exists>X. Alpha X \<and> Bet A X' X)\<close> by blast
                  have "A Out X' Y'" 
                    by (metis False \<open>A Out Y' C \<and> (\<nexists>X. Alpha X \<and> Bet A Y' X)\<close> 
                        \<open>Beta C\<close> \<open>X' = A \<or> (\<exists>X. Alpha X \<and> Bet A X' X)\<close> 
                        \<open>\<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> Bet A X Y\<close> bet2_out_out bet_out_1 
                        l6_6 not_bet_distincts out_diff1)
                  hence "Y' Out A X'" 
                    by (metis Bet_cases Out_def \<open>A Out Y' C \<and> (\<nexists>X. Alpha X \<and> Bet A Y' X)\<close> 
                        \<open>Alpha X\<close> \<open>Bet A X' X\<close> between_exchange4)
                  thus ?thesis 
                    by (simp add: \<open>A Out X' Y'\<close> out2__bet out_diff2)
                qed
              }
              ultimately 
              have "\<exists> B. \<forall> X Y. (Alpha'Fun A Alpha X \<and> Beta'Fun A C Alpha Y) \<longrightarrow> Bet X B Y"
                using DedekindVariant_def by (metis assms)            
              thus ?thesis by blast 
            qed
            moreover 
            let ?Alpha' = "Alpha'Fun A Alpha"
            let ?Beta' = "Beta'Fun A C Alpha"
            {
              assume "\<exists> B. \<forall> X Y. ?Alpha' X \<and> ?Beta' Y \<longrightarrow>Bet X B Y" 
              then obtain B where "\<forall> X Y. ?Alpha' X \<and> ?Beta' Y \<longrightarrow>Bet X B Y" 
                by blast
              {
                fix X Y
                assume "Alpha X" and "Beta Y" 
                have "?Alpha' X" 
                  using \<open>Alpha X\<close> between_trivial Alpha'Fun_def by auto
                moreover
                have "A Out Y C \<and> \<not> (\<exists> X::TPoint. Alpha X \<and> Bet A Y X)"
                  by (metis False Out_def True \<open>Beta C\<close> \<open>Beta Y\<close> 
                      \<open>\<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> Bet A X Y\<close> \<open>\<not> Beta A\<close> between_equality_2 l6_7)
                hence "Beta'Fun A C Alpha Y" 
                  using Beta'Fun_def by simp
                ultimately have "Bet X B Y" 
                  by (simp add: \<open>\<forall>X Y. Alpha'Fun A Alpha X \<and> Beta'Fun A C Alpha Y \<longrightarrow> Bet X B Y\<close>)
              }
              hence ?thesis 
                by blast
            }
            ultimately show ?thesis 
              by fast
          next
            case False
            thus ?thesis 
              using not_bet_distincts by blast
          qed
        qed
      next
        case False
        thus ?thesis 
          by blast
      qed
    qed
  }
  thus ?thesis
    using DedekindsAxiom_def by blast
qed

lemma dedekind_equiv: 
  shows "DedekindsAxiom \<longleftrightarrow> DedekindVariant" 
  using dedekind_equiv_R1 dedekind_equiv_R2 by blast

subsubsection "First Order Dedekind and Circle Circle"

definition Eq ::
  "[TPoint,TPoint] \<Rightarrow> bool"
  (" _ Eq _" [99,99] 50)
  where
    "A Eq B \<equiv> A = B"

inductive FOF :: "bool \<Rightarrow> bool" 
  where
    eq_fof : "FOF (A Eq B)" for A B :: TPoint
  | bet_fof : "FOF (Bet A B C)" for A B C :: TPoint
  | cong_fof : "FOF (Cong A B C D)" for A B C D :: TPoint
  | not_fof : "FOF (\<not> P)" if "FOF P" for P :: bool
  | and_fof : "FOF (P \<and> Q)" if "FOF P" and "FOF Q" for P Q :: bool
  | or_fof : "FOF (P \<or> Q)" if "FOF P" and "FOF Q" for P Q :: bool
  | implies_fof: "FOF (P \<longrightarrow> Q)" if "FOF P" and "FOF Q" for P Q :: bool 
  | forall_fof : "FOF (\<forall> A::TPoint. P A)" if "\<forall> A. FOF (P A)" for P :: "TPoint \<Rightarrow> bool"
    (*  | exists_fof : "FOF (\<exists> A::TPoint. P A)" if "\<exists> A. FOF (P A)" for P :: "TPoint \<Rightarrow> bool" *)
  | exists_fof : "FOF (\<exists> A::TPoint. P A)" if "FOF (P A)" for P :: "TPoint \<Rightarrow> bool"

definition FirstOrderDedekind :: bool
  ("FirstOrderDedeking" 50)
  where
    "FirstOrderDedekind \<equiv> 
\<forall> Alpha Beta :: TPoint\<Rightarrow>bool.
  (\<forall> X ::TPoint. FOF (Alpha X)) \<and> 
  (\<forall> Y ::TPoint. FOF (Beta Y)) \<and>
  (\<exists> A. \<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet A X Y)
\<longrightarrow>
  (\<exists> B. \<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet X B Y)"

end

context Tarski_neutral_dimensionless

begin

lemma dedekind__fod: 
  assumes "DedekindsAxiom" 
  shows "FirstOrderDedekind" 
  using DedekindsAxiom_def assms FirstOrderDedekind_def by blast

(** This proof is inspired by Franz Rothe's proof of Theorem 8.5 in Several topics from geometry *)

lemma circle_circle_aux: 
  assumes "\<forall> A B C D P Q. (P OnCircle C D \<and> Q OnCircle C D \<and> 
             P InCircleS A B \<and> Q OutCircleS A B \<and> 
             (A C OS P Q \<or> (Col P A C \<and> \<not> Col Q A C) \<or> (\<not> Col P A C \<and> Col Q A C )) \<longrightarrow>
            (\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D))" 
  shows "circle_circle"
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "Q OnCircle C D" and "P InCircleS A B" and 
      "Q OutCircleS A B" and "Coplanar A C P Q" and "\<not> Col P A C \<or> \<not> Col Q A C"
    have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
    proof (cases "Col P A C")
      case True
      hence "\<not> Col Q A C" 
        using \<open>\<not> Col P A C \<or> \<not> Col Q A C\<close> by auto
      hence "A C OS P Q \<or> (Col P A C \<and> \<not> Col Q A C) \<or> (\<not> Col P A C \<and> Col Q A C)" 
        using True by auto
      thus ?thesis using assms
          \<open>P OnCircle C D\<close>\<open>Q OnCircle C D\<close>\<open>P InCircleS A B\<close> 
          \<open>Q OutCircleS A B\<close> by blast
    next
      case False
      hence "\<not> Col P A C" 
        by simp
      show ?thesis 
      proof (cases "Col Q A C")
        case True
        then show ?thesis 
          using assms False \<open>P InCircleS A B\<close> \<open>P OnCircle C D\<close> \<open>Q OnCircle C D\<close> 
            \<open>Q OutCircleS A B\<close> by blast
      next
        case False
        hence "\<not> Col Q A C" 
          by simp
        hence "A C TS P Q \<or> A C OS P Q" 
          using cop__one_or_two_sides \<open>Coplanar A C P Q\<close> \<open>\<not> Col P A C\<close> by blast
        moreover {
          assume "A C TS P Q"
          obtain P' where "P P' Reflect A C" 
            using l10_6_existence by blast
          have "P' OnCircle C D" 
            by (meson OnCircle_def \<open>P OnCircle C D\<close> \<open>P P' Reflect A C\<close> 
                image_triv is_image_rev l10_10 onc2__cong)
          moreover have "P' InCircleS A B" 
            by (meson InCircleS_def OnCircle_def OutCircleS_def \<open>P InCircleS A B\<close>
                \<open>P P' Reflect A C\<close> circle_cases cong__nlt image_triv l10_10 lt_transitivity 
                not_cong_4321 onc2__cong)
          moreover have "A C TS P' P" 
            by (metis \<open>P P' Reflect A C\<close> \<open>\<not> Col P A C\<close> bet_col between_trivial l10_14 l10_8 l9_2)
          hence "A C OS P' Q" 
            using OS_def \<open>A C TS P Q\<close> l9_2 by blast
          hence "A C OS P' Q \<or> Col P' A C \<and> \<not> Col Q A C \<or> \<not> Col P' A C \<and> Col Q A C" 
            by blast
          have ?thesis using assms \<open>A C OS P' Q\<close> \<open>Q OnCircle C D\<close> \<open>Q OutCircleS A B\<close>
              calculation(1) calculation(2) by blast
        }
        moreover have "A C OS P Q \<longrightarrow> ?thesis" 
          using assms \<open>P InCircleS A B\<close> \<open>P OnCircle C D\<close> \<open>Q OnCircle C D\<close> 
            \<open>Q OutCircleS A B\<close> by blast
        ultimately show ?thesis 
          by blast
      qed
    qed
  }
  moreover
  {
    assume H1: "\<forall> A B C D P Q. P OnCircle C D \<and> Q OnCircle C D \<and> 
                               P InCircleS A B \<and> Q OutCircleS A B \<and>
                               Coplanar A C P Q \<and> (\<not> Col P A C \<or> \<not> Col Q A C) 
               \<longrightarrow> (\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D)" 
    {
      fix A B C D P Q
      assume "P OnCircle C D" and "Q OnCircle C D" and "P InCircle A B" and "Q OutCircle A B"
      have "\<exists> Q'. Q' OnCircle C D \<and> Q' OutCircle A B \<and> Col Q' A C" 
      proof -
        obtain Q' where "Bet A C Q'" and "Cong C Q' C D" 
          using segment_construction by blast
        have "Q' OnCircle C D" 
          by (simp add: OnCircle_def \<open>Cong C Q' C D\<close>)
        moreover have "A Q Le A Q'" 
          using \<open>Bet A C Q'\<close> \<open>Q OnCircle C D\<close> calculation onc2__cong triangle_inequality by auto
        hence "Q' OutCircle A B" 
          using OutCircle_def \<open>Q OutCircle A B\<close> le_transitivity by blast
        moreover have "Col Q' A C" 
          by (simp add: Col_def \<open>Bet A C Q'\<close>)
        ultimately show ?thesis by blast
      qed
      then obtain Q'' where "Q'' OnCircle C D" and "Q'' OutCircle A B" and "Col Q'' A C" 
        by blast
      have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D"
      proof (cases "Cong A P A B")
        case True
        then show ?thesis 
          using OnCircle_def \<open>P OnCircle C D\<close> by blast
      next
        case False
        hence "\<not> Cong A P A B"
          by simp
        show ?thesis 
        proof (cases "Cong A B A Q''")
          case True
          then show ?thesis 
            using OnCircle_def \<open>Q'' OnCircle C D\<close> onc_sym by blast
        next
          case False
          hence "\<not> Cong A B A Q''" 
            by simp
          have "A P Le A B" 
            using InCircle_def \<open>P InCircle A B\<close> by auto
          hence "A P Lt A B" 
            by (simp add: Lt_def \<open>\<not> Cong A P A B\<close>)
          hence "P InCircleS A B" 
            using InCircleS_def by blast
          have "Q'' OutCircleS A B" 
            using False Lt_def OutCircleS_def OutCircle_def \<open>Q'' OutCircle A B\<close> by blast
          {
            assume "A = C"
            have "A B Lt A P" 
              using OutCircleS_def \<open>A = C\<close> \<open>P OnCircle C D\<close> \<open>Q'' OnCircle C D\<close> 
                \<open>Q'' OutCircleS A B\<close> cong2_lt__lt cong_reflexivity onc2__cong by blast
            hence False 
              using \<open>A P Lt A B\<close> not_and_lt by blast
          }
          hence "A \<noteq> C" 
            by blast
          {
            assume "C = D"
            hence "A C Lt A B \<and> A B Lt A C" 
              using OnCircle_def OutCircleS_def \<open>A P Lt A B\<close> \<open>P OnCircle C D\<close> 
                \<open>Q'' OnCircle C D\<close> \<open>Q'' OutCircleS A B\<close> cong_identity by blast
            hence False 
              using lt__le lt__nle by blast
          }
          hence "C \<noteq> D" 
            by blast
          show ?thesis 
          proof (cases "Col P A C")
            case True
            obtain R where "Per A C R" and "Cong C R C D" 
              using exists_cong_per by blast
            hence "C \<noteq> R" 
              using \<open>C \<noteq> D\<close> cong_diff_3 by blast
            hence "A \<noteq> R" 
              using \<open>Per A C R\<close> l8_8 by blast
            have "\<not> Col A C R" 
              using \<open>A \<noteq> C\<close> \<open>C \<noteq> R\<close> \<open>Per A C R\<close> col_permutation_1 l8_8 per_col by blast
            have "R OnCircle A B \<longrightarrow> ?thesis" 
              using OnCircle_def \<open>Cong C R C D\<close> by auto
            have "Coplanar A C R Q''" 
              using Col_cases \<open>Col Q'' A C\<close> ncop__ncols by blast
            have "Coplanar A C P R" 
              using True ncop__ncol not_col_permutation_2 by blast
            have "\<not> Col R A C \<or> \<not> Col Q A C" 
              using Col_cases \<open>\<not> Col A C R\<close> by blast
            have "\<not> Col P A C \<or> \<not> Col R A C" 
              using Col_cases \<open>\<not> Col A C R\<close> by blast
            have "R OnCircle C D" 
              by (simp add: OnCircle_def \<open>Cong C R C D\<close>)
            hence "R InCircleS A B \<longrightarrow> ?thesis" 
              using H1 Col_cases \<open>Coplanar A C R Q''\<close> \<open>Q'' OnCircle C D\<close>
                \<open>Q'' OutCircleS A B\<close> \<open>\<not> Col A C R\<close> by blast
            moreover have "R OutCircleS A B \<longrightarrow> ?thesis" 
              using H1 \<open>Coplanar A C P R\<close> \<open>P InCircleS A B\<close> \<open>P OnCircle C D\<close> 
                \<open>R OnCircle C D\<close> \<open>\<not> Col P A C \<or> \<not> Col R A C\<close> by blast
            ultimately show ?thesis 
              using \<open>R OnCircle C D\<close> circle_cases by blast
          next
            case False
            moreover have "Coplanar A C P Q''" 
              using NCol_cases \<open>Col Q'' A C\<close> ncop__ncols by blast
            ultimately show ?thesis 
              using H1 \<open>P OnCircle C D\<close> \<open>Q'' OnCircle C D\<close> \<open>P InCircleS A B\<close> 
                \<open>Q'' OutCircleS A B\<close> by blast
          qed
        qed
      qed
    }
    hence "circle_circle" 
      using circle_circle_def 
      by blast
  }
  ultimately show ?thesis by blast
qed

definition AlphaFun:: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> 
                       TPoint \<Rightarrow> TPoint \<Rightarrow> (TPoint \<Rightarrow> bool)"
  where
    "AlphaFun A B C D P Q \<equiv> 
     \<lambda> X. Bet P X Q \<and> (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B)"

definition BetaFun:: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> 
                      TPoint \<Rightarrow>TPoint \<Rightarrow> (TPoint \<Rightarrow> bool)"
  where
    "BetaFun A B C D P Q \<equiv> 
     \<lambda> Y. Bet P Y Q \<and> (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B)"

definition DedekindLemFun:: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> 
                             TPoint \<Rightarrow>TPoint \<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" 
  where
    "DedekindLemFun \<equiv> 
     \<lambda> A B C D P Q. \<lambda> R. \<lambda> X Y. (Bet P X Q \<and> 
                           (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B) \<and>
                           Bet P Y Q \<and> 
                           (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B)) 
      \<longrightarrow>
    Bet X R Y"

lemma fod__circle_circle:
  assumes FirstOrderDedekind 
  shows CircleCircle 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "Q OnCircle C D" and "P InCircleS A B" and "Q OutCircleS A B" 
      and "A C OS P Q \<or> (Col P A C \<and> \<not> Col Q A C) \<or> (\<not> Col P A C \<and> Col Q A C )" 
    have "A \<noteq> C" 
      using \<open>A C OS P Q \<or> Col P A C \<and> \<not> Col Q A C \<or> \<not> Col P A C \<and> Col Q A C\<close> 
        col_trivial_2 os_distincts by blast
    {
      assume "P = Q"
      have "A P Lt A B" 
        using InCircleS_def \<open>P InCircleS A B\<close> by force
      have "A B Lt A P" 
        using OutCircleS_def \<open>P = Q\<close> \<open>Q OutCircleS A B\<close> by fastforce
      hence False 
        using not_and_lt 
        using \<open>A P Lt A B\<close> by blast
    }
    hence "P \<noteq> Q" 
      by blast
    hence "C \<noteq> D" 
      using \<open>P OnCircle C D\<close> \<open>Q OnCircle C D\<close> inc_eq onc__inc by blast
    {
      fix X Y
      assume "Bet P X Q" and "Bet P Y Q" and
        "X \<noteq> P" and "X \<noteq> Q" and "Y \<noteq> P" and "Y \<noteq> Q"
      have "A C OS P Q \<longrightarrow> A C OS X Y" 
        by (meson \<open>Bet P X Q\<close> \<open>Bet P Y Q\<close> l9_17 one_side_symmetry one_side_transitivity)
      moreover {
        assume "Col P A C" and "\<not> Col Q A C" 
        have "A C OS Q X" 
          by (metis \<open>Bet P X Q\<close> \<open>Col P A C\<close> \<open>X \<noteq> P\<close> \<open>\<not> Col Q A C\<close> bet_col 
              bet_out colx not_col_permutation_1 one_side_symmetry out_one_side_1)
        moreover have "A C OS Q Y" 
          by (metis \<open>Bet P Y Q\<close> \<open>Col P A C\<close> \<open>Y \<noteq> P\<close> \<open>\<not> Col Q A C\<close> bet_col 
              bet_out colx not_col_permutation_2 one_side_symmetry out_one_side_1)
        ultimately have "A C OS X Y" 
          using one_side_symmetry one_side_transitivity by blast
      }
      moreover {
        assume "\<not> Col P A C" and "Col Q A C" 
        have "A C OS P X" 
          by (metis \<open>Bet P X Q\<close> \<open>Col Q A C\<close> \<open>X \<noteq> Q\<close> \<open>\<not> Col P A C\<close> bet_col 
              bet_col1 bet_out_1 l6_21 l9_19_R2 not_col_permutation_1 one_side_symmetry)
        moreover have "A C OS P Y" 
          by (metis \<open>Bet P Y Q\<close> \<open>Col Q A C\<close> \<open>Y \<noteq> Q\<close> \<open>\<not> Col P A C\<close> bet_col 
              bet_col1 bet_out_1 l6_21 not_col_permutation_1 
              one_side_symmetry out_one_side_1) 
        ultimately have "A C OS X Y"
          using one_side_symmetry one_side_transitivity by blast
      }
      ultimately have "A C OS X Y" 
        using \<open>A C OS P Q \<or> Col P A C \<and> \<not> Col Q A C \<or> \<not> Col P A C \<and> Col Q A C\<close> by fastforce
    }
    {
      fix X Y
      assume "Bet P Y Q" and "Bet P X Y"
      hence "\<not> A C TS X Y" 
        by (metis TS_def \<open>A C OS P Q \<or> Col P A C \<and> \<not> Col Q A C \<or> \<not> Col P A C \<and> Col Q A C\<close> 
            bet_ts__ts between_symmetry l9_2 one_side_chara)
    }
    have "A C P LtA A C Q" 
    proof -
      have "C \<noteq> Q" 
        using \<open>C \<noteq> D\<close> \<open>Q OnCircle C D\<close> onc_not_center by blast
      moreover have "Cong C Q C P" 
        using \<open>P OnCircle C D\<close> \<open>Q OnCircle C D\<close> onc2__cong by auto
      moreover have "P A Lt Q A" 
        by (meson InCircleS_def OutCircleS_def \<open>P InCircleS A B\<close>
            \<open>Q OutCircleS A B\<close> lt_comm lt_transitivity)
      ultimately show ?thesis 
        using \<open>A \<noteq> C\<close> cong_reflexivity t18_19 by auto
    qed
    hence "\<not> A C P CongA A C Q" 
      using lta_not_conga by auto
    {
      assume "Col P Q C"
      {
        assume "A C OS P Q" 
        hence "A C P CongA A C Q" 
          by (metis NCol_cases TS_def \<open>A C P LtA A C Q\<close> \<open>Col P Q C\<close> 
              invert_one_side lta_os__ts one_side_symmetry) 
        hence False 
          by (simp add: \<open>\<not> A C P CongA A C Q\<close>)
      }
      moreover {
        assume "Col P A C" and "\<not> Col Q A C" 
        hence False 
          by (metis \<open>C \<noteq> D\<close> \<open>Col P Q C\<close> \<open>P OnCircle C D\<close> col_permutation_1 
              col_transitivity_2 onc_not_center)
      }
      moreover {
        assume "\<not> Col P A C" and "Col Q A C" 
        hence False 
          by (metis \<open>C \<noteq> D\<close> \<open>Col P Q C\<close> \<open>Q OnCircle C D\<close> 
              col_permutation_1 col_transitivity_2 onc_not_center)
      }
      ultimately have False 
        using \<open>A C OS P Q \<or> Col P A C \<and> \<not> Col Q A C \<or> \<not> Col P A C \<and> Col Q A C\<close> by fastforce
    }
    hence "\<not> Col P Q C" 
      by auto
    { 
      fix X Y X0 Y0
      assume "Bet P Y Q" and "X \<noteq> Y" and
        "X0 OnCircle C D" and "C Out X X0" and
        "Y0 OnCircle C D" and "C Out Y Y0" and "Bet P X Y"
      have "Cong C Y0 C X0" 
        using \<open>X0 OnCircle C D\<close> \<open>Y0 OnCircle C D\<close> onc2__cong by auto
      moreover have "X0 C A LtA Y0 C A" 
      proof (rule conga_preserves_lta [where ?A="A" and ?B="C" and ?C="X" and 
            ?D="A" and ?E="C" and ?F="Y"])
        show "A C X CongA X0 C A" 
          by (simp add: Out_cases \<open>A \<noteq> C\<close> \<open>C Out X X0\<close> conga_right_comm 
              out2__conga out_trivial)
        show "A C Y CongA Y0 C A " 
          by (simp add: \<open>A \<noteq> C\<close> \<open>C Out Y Y0\<close> conga_right_comm 
              conga_sym_equiv out2__conga out_trivial)
        show "A C X LtA A C Y"
        proof -
          have "X InAngle Y C A" 
          proof (rule in_angle_trans [where ?D="P"])
            show "X InAngle Y C P"
              by (metis InAngle_def Out_def \<open>Bet P X Y\<close> \<open>C Out X X0\<close> 
                  \<open>C Out Y Y0\<close> \<open>\<not> Col P Q C\<close> between_symmetry col_trivial_2 
                  not_col_permutation_1 out_trivial)
            show "P InAngle Y C A"
            proof (rule in_angle_trans2 [where ?A="Q"])
              show " Y InAngle Q C P"
                by (metis InAngle_def Out_def \<open>Bet P Y Q\<close> \<open>C Out Y Y0\<close> 
                    \<open>\<not> Col P Q C\<close> between_symmetry not_col_distincts out_trivial)
              show "P InAngle Q C A"
              proof -
                have "A C OS P Q \<longrightarrow> ?thesis" 
                  by (meson \<open>A C P LtA A C Q\<close> invert_one_side l11_24 lta_os__ts 
                      one_side_symmetry os_ts__inangle)
                moreover {
                  assume "Col P A C" and
                    "\<not> Col Q A C"
                  hence "C Out A P" 
                    using \<open>A C P LtA A C Q\<close> col_lta__out col_permutation_1 by blast
                  hence ?thesis 
                    by (metis \<open>\<not> Col P Q C\<close> col_trivial_2 out341__inangle)
                }
                moreover {
                  assume "\<not> Col P A C" and "Col Q A C"
                  {
                    assume "C Out A Q"
                    have "A C Q LeA A C P" 
                      using NCol_perm \<open>A C P LtA A C Q\<close> \<open>C Out A Q\<close> \<open>Col Q A C\<close> 
                        col_lta__bet not_bet_and_out by blast
                    hence False 
                      using \<open>A C P LtA A C Q\<close> lea__nlta by auto
                  }
                  hence "\<not> C Out A Q"
                    by blast
                  hence "Bet Q C A" 
                    using \<open>Col Q A C\<close> between_symmetry col_permutation_1 l6_4_2 by blast
                  hence ?thesis 
                    using InAngle_def \<open>A \<noteq> C\<close> \<open>Y InAngle Q C P\<close> by auto
                }
                ultimately show ?thesis 
                  using \<open>A C OS P Q \<or> Col P A C \<and> \<not> Col Q A C \<or> \<not> Col P A C \<and> Col Q A C\<close> 
                  by blast
              qed
            qed
          qed
          hence "X InAngle A C Y" 
            using l11_24 by blast

          hence "A C X LeA A C Y" 
            by (simp add: inangle__lea)
          moreover 
          {
            assume "A C X CongA A C Y"
            moreover have" Coplanar A C X Y" 
              using \<open>X InAngle A C Y\<close> coplanar_perm_8 inangle__coplanar by blast
            ultimately have "C Out X Y \<or> A C TS X Y"  
              using conga_cop__or_out_ts [where ?A="A" and ?B="C" and ?C="X" and ?C'="Y"] 
              by blast
            moreover have "C Out X Y \<longrightarrow> False" 
              by (metis Col_def NCol_perm \<open>Bet P X Y\<close> \<open>Bet P Y Q\<close> \<open>X \<noteq> Y\<close> 
                  \<open>\<not> Col P Q C\<close> between_exchange3 l6_16_1 out_col)
            moreover have "A C TS X Y \<longrightarrow> False" 
              by (simp add: \<open>Bet P X Y\<close> \<open>Bet P Y Q\<close> 
                  \<open>\<And>Y X. \<lbrakk>Bet P Y Q; Bet P X Y\<rbrakk> \<Longrightarrow> \<not> A C TS X Y\<close>)
            ultimately have False 
              by blast 
          }
          hence "\<not> A C X CongA A C Y" 
            by blast
          ultimately show ?thesis
            using LtA_def by blast
        qed
      qed
      ultimately have "A X0 Lt A Y0" 
        using cong_reflexivity t18_18 by blast
    }
    hence 1: "\<forall> X Y X0 Y0. Bet P Y Q \<and> X \<noteq> Y \<and> X0 OnCircle C D \<and> C Out X X0 \<and> 
                           Y0 OnCircle C D \<and> C Out Y Y0 \<and> Bet P X Y \<longrightarrow> A X0 Lt A Y0"
      by blast
    have "\<exists> R. \<forall> X Y.
    (Bet P X Q \<and> (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B) \<and>
    Bet P Y Q \<and> (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B) \<longrightarrow>
    Bet X R Y)" 
    proof -
      {
        fix X
        have "((AlphaFun A B C D P Q) X) 
              = (Bet P X Q \<and> (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B))"
          using AlphaFun_def by simp
        have "FOF (Bet P X Q)" 
          by (simp add: bet_fof)
        moreover have "FOF (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B)" 
        proof (cases "\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B")
          case True
          then obtain X0 where "X0 OnCircle C D" and "C Out X X0" and "X0 InCircle A B" 
            by auto
          have "FOF (X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B)" 
          proof -
            have "FOF (X0 OnCircle C D)" 
              using \<open>X0 OnCircle C D\<close> calculation implies_fof by fastforce
            moreover have "FOF (C Out X X0)" 
              using \<open>C Out X X0\<close> \<open>X0 OnCircle C D\<close> calculation by auto
            moreover have "FOF (X0 InCircle A B)" 
              using \<open>C Out X X0\<close> \<open>X0 InCircle A B\<close> calculation(2) by auto
            ultimately show ?thesis 
              using and_fof by auto
          qed
          thus ?thesis
            using exists_fof \<open>C Out X X0\<close> \<open>X0 InCircle A B\<close> \<open>X0 OnCircle C D\<close> by fast
        next
          case False
          hence "\<forall> X0. \<not>(X0 OnCircle C D) \<or> \<not> (C Out X X0) \<or> \<not> (X0 InCircle A B)" 
            by blast
          {
            fix X0
            have "\<not>(X0 OnCircle C D) 
                  \<longrightarrow> FOF (\<not> (X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B))" 
              using calculation implies_fof by fastforce 
            moreover have "\<not> (C Out X X0) 
                           \<longrightarrow> FOF (\<not> (X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B))" 
              using \<open>FOF (Bet P X Q)\<close> implies_fof by fastforce
            moreover have "\<not> (X0 InCircle A B) 
                           \<longrightarrow> FOF (\<not> (X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B))" 
              using \<open>FOF (Bet P X Q)\<close> implies_fof by fastforce
            ultimately have "FOF (\<not> (X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B))" 
              using False by blast
          }
          hence "FOF (\<forall> X0. \<not>(X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B))" 
            using False by auto
          hence "FOF (\<not> (\<exists> X0. (X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B)))" 
            by force
          hence "FOF (\<not> (\<not> (\<exists> X0. (X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B))))" 
            using not_fof by blast
          thus ?thesis 
            by argo
        qed
        ultimately 
        have "FOF (Bet P X Q \<and> (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B))" 
          using and_fof by blast
      }
      hence "\<forall> X::TPoint. FOF ((AlphaFun A B C D P Q) X)"
        using AlphaFun_def by simp
      moreover
      {
        fix Y::TPoint
        have "((BetaFun A B C D P Q) Y) 
               = (Bet P Y Q \<and> (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B))"
          using BetaFun_def by simp
        have "FOF (Bet P Y Q)" 
          by (simp add: bet_fof)
        moreover
        have "FOF (\<exists> X0. X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B)" 
        proof (cases "\<exists> X0. X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B")
          case True
          then obtain X0 where "X0 OnCircle C D" and "C Out Y X0" and "X0 OutCircle A B" 
            by auto
          show ?thesis 
          proof -
            have "FOF (X0 OnCircle C D)" 
              using \<open>X0 OnCircle C D\<close> calculation implies_fof by fastforce
            moreover have "FOF (C Out Y X0)" 
              using \<open>C Out Y X0\<close> \<open>X0 OnCircle C D\<close> calculation by auto
            ultimately have "FOF (X0 OnCircle C D \<and> C Out Y X0)" 
              using and_fof by blast
            moreover have "FOF (X0 OutCircle A B)"
              using \<open>X0 OutCircle A B\<close> calculation implies_fof by force
            hence "FOF (X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B)" 
              using \<open>C Out Y X0\<close> \<open>X0 OnCircle C D\<close> by auto
            thus ?thesis using exists_fof by fast
          qed
        next
          case False
          hence "\<not> (\<exists> X0. X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B)" 
            by blast
          hence "\<forall> X0. \<not>(X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B)" 
            by blast
          hence "\<forall> X0. \<not>(X0 OnCircle C D) \<or> \<not> (C Out Y X0) \<or> \<not> (X0 OutCircle A B)" 
            by blast
          {
            fix X0
            have "\<not>(X0 OnCircle C D) 
                  \<longrightarrow> FOF (\<not> (X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B))" 
              using calculation implies_fof by fastforce 
            moreover have "\<not> (C Out Y X0) 
                           \<longrightarrow> FOF (\<not> (X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B))" 
              using \<open>FOF (Bet P Y Q)\<close> implies_fof by fastforce
            moreover have "\<not> (X0 OutCircle A B) 
                           \<longrightarrow> FOF (\<not> (X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B))" 
              using \<open>FOF (Bet P Y Q)\<close> implies_fof by fastforce
            ultimately have "FOF (\<not> (X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B))" 
              using False by blast
          }
          hence "FOF (\<forall> X0. \<not>(X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B))" 
            using False by auto
          hence "FOF (\<not> (\<exists> X0. (X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B)))" 
            by force
          hence "FOF (\<not> (\<not> (\<exists> X0. (X0 OnCircle C D \<and> C Out Y X0 \<and> X0 OutCircle A B))))" 
            using not_fof by blast
          thus ?thesis 
            by argo
        qed
        ultimately have "FOF (Bet P Y Q \<and> 
                             (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B))" 
          using and_fof by blast
        hence "FOF ((BetaFun A B C D P Q) Y)" 
          using \<open>BetaFun A B C D P Q Y 
                 = (Bet P Y Q \<and> (\<exists>Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B ))\<close> 
          by force 
      }
      hence "\<forall> Y::TPoint. FOF ((BetaFun A B C D P Q) Y)" 
        using forall_fof BetaFun_def by simp
      moreover
      have "\<exists> R. (\<forall> X Y. ((AlphaFun A B C D P Q) X) \<and> ((BetaFun A B C D P Q) Y) \<longrightarrow> Bet R X Y)"
      proof -
        {
          fix X Y
          assume "(AlphaFun A B C D P Q) X" and
            "(BetaFun A B C D P Q) Y"
          have "Bet P X Q \<and> (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B)"
            using \<open>(AlphaFun A B C D P Q) X\<close> AlphaFun_def by auto
          then obtain X0 where "X0 OnCircle C D" and "C Out X X0" and "X0 InCircle A B" 
            by blast
          have "Bet P Y Q \<and> (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B)"
            using \<open>(BetaFun A B C D P Q) Y\<close> BetaFun_def by auto
          then obtain Y0 where "Y0 OnCircle C D" and "C Out Y Y0" and "Y0 OutCircle A B"
            by blast
          have "Bet P X Q" 
            using \<open>(AlphaFun A B C D P Q) X\<close> AlphaFun_def by simp
          moreover have "Bet P Y Q" 
            using \<open>(BetaFun A B C D P Q) Y\<close> BetaFun_def by simp
          moreover {
            assume "Bet P Y X"
            have "Bet P X Y"
            proof (cases "X = Y")
              case True
              thus ?thesis 
                using \<open>Bet P Y X\<close> by blast
            next
              case False
              hence "X \<noteq> Y" 
                by simp
              moreover have "A Y0 Lt A X0"
                using 1 by (metis False \<open>Bet P X Q\<close> \<open>C Out X X0\<close> \<open>C Out Y Y0\<close>
                    \<open>Bet P Y X\<close>\<open>X0 OnCircle C D\<close>\<open>Y0 OnCircle C D\<close>)
              moreover have "A X0 Le A Y0" 
                using InCircle_def OutCircle_def \<open>X0 InCircle A B\<close> 
                  \<open>Y0 OutCircle A B\<close> le_transitivity by blast
              ultimately show ?thesis 
                using le__nlt by blast
            qed
          }
          ultimately have "Bet P X Y" using l5_3 by blast
        }
        thus ?thesis by blast
      qed
      moreover
      hence "\<exists> R. \<forall> X Y. (Bet P X Q \<and> 
                         (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B) \<and>
                          Bet P Y Q \<and> 
                          (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B) 
             \<longrightarrow> Bet R X Y)" 
        using AlphaFun_def BetaFun_def by auto
      ultimately have "\<exists> R. (\<forall> X Y. ((AlphaFun A B C D P Q) X) \<and> ((BetaFun A B C D P Q) Y) 
                       \<longrightarrow> Bet X R Y)" 
        using assms(1) FirstOrderDedekind_def AlphaFun_def BetaFun_def by blast
      thus ?thesis 
        using AlphaFun_def BetaFun_def by simp
    qed
    hence "\<exists> R. \<forall> X Y. ((Bet P X Q \<and> (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B) \<and>
                         Bet P Y Q \<and> (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B)) 
                         \<longrightarrow> Bet X R Y)" by blast
    hence "\<exists> R. \<forall> X Y. DedekindLemFun A B C D P Q R X Y"
      using DedekindLemFun_def by presburger
    then obtain R where "\<forall> X Y. DedekindLemFun A B C D P Q R X Y"
      by blast
    hence "\<forall> X Y. Bet P X Q \<and> (\<exists> X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B) \<and>
                  Bet P Y Q \<and> (\<exists> Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B) 
                  \<longrightarrow> Bet X R Y" 
      using DedekindLemFun_def by simp
    moreover
    have "\<exists> X0. X0 OnCircle C D \<and> C Out P X0 \<and> X0 InCircle A B" 
      using \<open>C \<noteq> D\<close> \<open>P InCircleS A B\<close> \<open>P OnCircle C D\<close> incs__inc 
        onc_not_center out_trivial by blast
    moreover
    then obtain X0 where "X0 OnCircle C D" and "C Out P X0" and "X0 InCircle A B" 
      by blast
    have "\<exists> Y0. Y0 OnCircle C D \<and> C Out Q Y0 \<and> Y0 OutCircle A B" 
      using \<open>Q OutCircleS A B\<close> \<open>Q OnCircle C D\<close> \<open>A C P LtA A C Q\<close> lta_distincts 
        out_trivial outcs__outc by blast
    moreover
    then obtain Y0 where "Y0 OnCircle C D" and "C Out Q Y0" and "Y0 OutCircle A B" 
      by blast
    have "Bet P P Q" 
      using between_trivial2 by auto
    moreover have "Bet P Q Q" 
      by (simp add: between_trivial)
    ultimately have "Bet P R Q" 
      using DedekindLemFun_def by blast
    have "R \<noteq> C" 
      using \<open>Bet P Q Q\<close> \<open>Bet P R Q\<close> \<open>\<not> Col P Q C\<close> bet_col1 by blast
    obtain Z where "Z OnCircle C D" and "C Out R Z" 
      using \<open>C \<noteq> D\<close> \<open>R \<noteq> C\<close> onc_exists by blast
    have "A \<noteq> B" 
      using \<open>P InCircleS A B\<close> inc__outc inc_eq incs__inc incs__noutc_1 by blast
    {
      assume "Z InCircleS A B"
      {
        assume "Q = R"
        hence "Q = Z" 
          by (metis OnCircle_def \<open>C Out R Z\<close> \<open>C \<noteq> D\<close> \<open>Q OnCircle C D\<close> 
              \<open>Z OnCircle C D\<close> between_cong between_trivial2 
              l6_11_uniqueness out_trivial)
        hence "\<not> Z OnCircle C D" 
          using outcs__ninc  \<open>Q OutCircleS A B\<close> \<open>Z InCircleS A B\<close> incs__inc by blast
        hence False 
          using \<open>Z OnCircle C D\<close> by auto
      }
      hence "Q \<noteq> R" by blast
      have "\<not> Col C Q R" 
        using Col_perm \<open>Bet P R Q\<close> \<open>Q \<noteq> R\<close> \<open>\<not> Col P Q C\<close> bet_col col2__eq by blast
      have "\<exists> T. T OnCircle A B \<and> Bet A Z T" 
        using \<open>Z InCircleS A B\<close> inc__radius incs__inc by blast
      then obtain T where "T OnCircle A B" and "Bet A Z T" 
        by blast
      have "T \<noteq> Z" 
        using \<open>T OnCircle A B\<close> \<open>Z InCircleS A B\<close> onc__outc outc__nincs_1 by blast
      obtain I where "Per I Z C" and "Cong I Z T Z" and "C R OS I Q" 
        using ex_per_cong by (metis Col_cases Col_def Out_def \<open>C Out R Z\<close>  
            \<open>T \<noteq> Z\<close> \<open>\<not> Col C Q R\<close>)
      hence "\<not> Col I Z C" 
        by (metis \<open>C Out R Z\<close> \<open>T \<noteq> Z\<close> cong_identity cong_symmetry out_distinct per_not_col)
      obtain X0 where "X0 OnCircle C D" and "C Out I X0" 
        by (metis \<open>C \<noteq> D\<close> \<open>\<not> Col I Z C\<close> col_trivial_3 onc_exists)
      have "C X0 Lt C I" 
      proof -
        {
          assume "Z C Lt I C"
          moreover have "Cong Z C C X0" 
            using Cong_cases \<open>X0 OnCircle C D\<close> \<open>Z OnCircle C D\<close> onc2__cong by blast
          moreover have "Cong I C C I" 
            by (simp add: cong_pseudo_reflexivity)
          ultimately have ?thesis 
            using cong2_lt__lt by blast
        }
        thus ?thesis 
          by (metis Col_def \<open>Per I Z C\<close> \<open>\<not> Col I Z C\<close> between_trivial2 lt_left_comm per_lt)
      qed
      have "X0 \<noteq> I" 
        using \<open>C X0 Lt C I\<close> nlt by auto
      have "\<not> Col I X0 Z" 
        by (metis Col_perm \<open>C Out I X0\<close> \<open>X0 \<noteq> I\<close> \<open>\<not> Col I Z C\<close> col2__eq out_col)
      have "Obtuse I X0 Z" 
      proof (rule acute_bet__obtuse [where ?A = "C"])
        show "Bet C X0 I" 
          by (metis Out_def \<open>C X0 Lt C I\<close> \<open>C Out I X0\<close> bet__lt1213 not_and_lt)
        show "I \<noteq> X0" 
          using \<open>X0 \<noteq> I\<close> by auto
        show "Acute C X0 Z" 
          by (metis Col_def \<open>X0 OnCircle C D\<close> \<open>C Out I X0\<close> \<open>Z OnCircle C D\<close> 
              \<open>\<not> Col I X0 Z\<close> between_trivial cong__acute onc2__cong out_distinct)
      qed
      hence "X0 Z Lt I Z" 
        by (metis \<open>X0 \<noteq> I\<close> \<open>\<not> Col I X0 Z\<close> col_trivial_2 l11_46)
      have "X0 InCircleS A B" 
      proof -
        have "Z X0 Le Z T" 
          by (meson \<open>Cong I Z T Z\<close> \<open>X0 Z Lt I Z\<close> cong__le3412 le__nlt 
              le_right_comm le_transitivity local.le_cases not_cong_3421)
        then obtain M where "Bet Z M T" and "Cong Z M Z X0" 
          using le_bet by blast
        {
          assume "M = T"
          have "Z M Lt Z M" 
          proof (rule cong2_lt__lt [where ?A = "X0" and ?B = "Z" and ?C = "I" and ?D = "Z"])
            show "X0 Z Lt I Z" 
              by (simp add: \<open>X0 Z Lt I Z\<close>)
            show "Cong X0 Z Z M" 
              using Cong_cases \<open>Cong Z M Z X0\<close> by blast
            show "Cong I Z Z M"
            proof (rule cong_transitivity [where ?C="T" and ?D="Z"])
              show "Cong I Z T Z" 
                by (simp add: \<open>Cong I Z T Z\<close>)
              show "Cong T Z Z M"
                using \<open>M = T\<close> cong_pseudo_reflexivity by auto 
            qed
          qed
          hence False 
            using nlt by auto
        }
        hence "M \<noteq> T" 
          by auto
        have "A X0 Le A M" 
          using \<open>Bet A Z T\<close> \<open>Bet Z M T\<close> \<open>Cong Z M Z X0\<close> between_inner_transitivity 
            cong_symmetry triangle_inequality by blast
        moreover have "A M Lt A T" 
          using \<open>Bet A Z T\<close> \<open>Bet Z M T\<close> \<open>M \<noteq> T\<close> bet__lt1213 between_exchange2 by blast
        hence "A M Lt A B" 
          using OnCircle_def \<open>T OnCircle A B\<close> cong2_lt__lt cong_reflexivity by blast
        ultimately show ?thesis 
          by (simp add: InCircleS_def le1234_lt__lt)
      qed
      have "X0 InAngle R C Q"
      proof (rule l11_25 [where ?P="X0" and ?A="Z" and ?C="Q"])
        show "X0 InAngle Z C Q" 
        proof -
          have "Z C X0 LeA Z C Q" 
          proof -
            have "Cong C Q C X0" 
              using \<open>Q OnCircle C D\<close> \<open>X0 OnCircle C D\<close> onc2__cong by blast
            moreover have "Cong C Z C Z" 
              by (simp add: cong_reflexivity)
            moreover 
            have "A T Le A Q" 
            proof (rule l5_6 [where ?A="A" and ?B="B" and ?C="A" and ?D="Q"]) 
              show "A B Le A Q"             
                using InCircle_def \<open>Q OutCircleS A B\<close> incs__inc incs__outcs_2 by blast
              show "Cong A B A T"             
                using \<open>T OnCircle A B\<close> onc212 onc2__cong by blast
              show "Cong A Q A Q"
                using cong_reflexivity by blast
            qed
            have "T Z Le Q Z" 
            proof (cases "A = Z")
              case True
              then show ?thesis 
                using Le_cases \<open>A T Le A Q\<close> by blast
            next
              case False
              obtain M where "Bet A T M" and "Cong A M A Q" 
                using \<open>A T Le A Q\<close> l5_5_1 by blast
              have "Bet A Z M" 
                using \<open>Bet A T M\<close> \<open>Bet A Z T\<close> between_exchange4 by blast
              have "T Z Le M Z" 
                using Bet_cases \<open>Bet A T M\<close> \<open>Bet A Z T\<close> bet__le2313 between_exchange3 by blast
              moreover have "A Out Z M" 
                using False \<open>Bet A Z M\<close> bet_out by force
              hence "M Z Le Q Z" 
                using Le_cases \<open>Cong A M A Q\<close> not_cong_3412 
                  triangle_reverse_inequality by blast
              ultimately show ?thesis 
                using le_transitivity by blast
            qed
            hence "I Z Le Q Z" 
              using \<open>Cong I Z T Z\<close> cong__le le_transitivity by blast
            hence "X0 Z Lt Q Z" 
              using \<open>X0 Z Lt I Z\<close> le3456_lt__lt by blast
            ultimately 
            show ?thesis 
              by (metis Cong_perm cong__le3412 cong_diff_3 le__nlt nlta__lea 
                  not_and_lt t18_18)
          qed
          moreover have "C R OS Q X0" 
            using \<open>C Out I X0\<close> \<open>C R OS I Q\<close> not_col_distincts one_side_symmetry 
              os_out_os by blast
          hence "Z C OS Q X0"
            by (metis Out_def \<open>C Out R Z\<close> col_one_side invert_one_side out_col)
          ultimately show ?thesis
            using lea_in_angle by blast
        qed
        show "C Out R Z" 
          by (simp add: \<open>C Out R Z\<close>)
        show "C Out Q Q" 
          using \<open>C Out Q Y0\<close> out_diff1 out_trivial by blast
        show "C Out X0 X0"
          using Out_def \<open>C Out I X0\<close> out_trivial by presburger
      qed
      then obtain X where "Bet R X Q" and "(X = C \<or> C Out X X0)" 
        using InAngle_def by auto
      moreover
      have "X = C \<longrightarrow> False" 
        using Col_def \<open>\<not> Col C Q R\<close> calculation(1) by auto
      moreover
      {
        assume "C Out X X0"
        have "\<exists> X1. X1 OnCircle C D \<and> C Out X X1 \<and> X1 InCircle A B" 
          using \<open>C Out X X0\<close> \<open>X0 InCircleS A B\<close> \<open>X0 OnCircle C D\<close> incs__inc by blast
        hence "Bet X R Q" 
          by (metis (full_types) Out_def \<open>Bet P Q Q\<close> \<open>Bet P R Q\<close> \<open>C Out Q Y0\<close> 
              \<open>Q OnCircle C D\<close> \<open>Q OutCircleS A B\<close> 
              \<open>\<forall>X Y. Bet P X Q \<and> (\<exists>X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B ) \<and> 
                   Bet P Y Q \<and> (\<exists>Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B ) 
             \<longrightarrow> Bet X R Y\<close> 
              between_exchange2 calculation(1) out_trivial outcs__outc)
        hence "X = R" 
          using between_equality calculation(1) by blast
        hence False 
          using Col_def \<open>C Out I X0\<close> \<open>C Out X X0\<close> \<open>C R OS I Q\<close> between_trivial 
            col123__nos os_out_os out_col by blast
      }
      ultimately
      have False 
        by blast
      hence "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D"  
        by blast
    }
    moreover
    {
      assume "Z OutCircleS A B"
      have "P \<noteq> R" by (metis OnCircle_def Out_def \<open>C Out R Z\<close> \<open>P InCircleS A B\<close> 
            \<open>P OnCircle C D\<close> \<open>Z OnCircle C D\<close> \<open>Z OutCircleS A B\<close> incs__inc 
            l6_11_uniqueness out_trivial outcs__ninc_1)
      hence "\<not> Col C P R" 
        using Col_def \<open>Bet P R Q\<close> \<open>\<not> Col P Q C\<close> col2__eq by blast
      obtain T where "T OnCircle A B" and "A Out Z T" 
        by (metis \<open>A \<noteq> B\<close> \<open>Z OutCircleS A B\<close> inc112 onc_exists outcs__ninc_1)
      have "A T Le A Z" proof (rule l5_6 [where ?A="A" and ?B="B" and ?C="A" and ?D="Z"])
        show "A B Le A Z" 
          using OutCircle_def \<open>Z OutCircleS A B\<close> outcs__outc by blast
        show "Cong A B A T"           
          using OnCircle_def \<open>T OnCircle A B\<close> not_cong_3412 by blast
        show "Cong A Z A Z"
          by (simp add: cong_reflexivity)
      qed
      hence "Bet A T Z" 
        by (simp add: \<open>A Out Z T\<close> l6_13_1 l6_6)
      {
        assume "T = Z"
        hence "\<not> Z InCircle A B" 
          using \<open>Z OutCircleS A B\<close> outcs__ninc by blast
        hence False 
          using \<open>T = Z\<close> \<open>T OnCircle A B\<close> onc__inc by blast
      }
      hence "T \<noteq> Z" 
        by auto
      obtain I where "Per I Z C" and "Cong I Z T Z" and "C R OS I P" 
        by (metis Col_cases Col_def Out_def \<open>C Out R Z\<close> \<open>T \<noteq> Z\<close> \<open>\<not> Col C P R\<close> ex_per_cong)
      hence "\<not> Col I Z C" 
        using \<open>C Out R Z\<close> \<open>T \<noteq> Z\<close> cong_reverse_identity l8_9 out_diff2 by blast
      obtain Y0 where "Y0 OnCircle C D" and "C Out I Y0" 
        by (metis \<open>C R OS I P\<close> \<open>C \<noteq> D\<close> onc_exists os_distincts)
      have "Z C Lt I C" 
        using \<open>Per I Z C\<close> \<open>\<not> Col I Z C\<close> l11_46 not_col_distincts by blast
      have "Cong Z C C Y0" 
        using Cong_cases \<open>Y0 OnCircle C D\<close> \<open>Z OnCircle C D\<close> onc2__cong by blast
      have "Cong I C C I" 
        by (simp add: cong_pseudo_reflexivity)
      hence "C Y0 Lt C I" 
        using \<open>Cong Z C C Y0\<close> \<open>Z C Lt I C\<close> cong2_lt__lt by blast
      have "Y0 \<noteq> I" 
        using \<open>C Y0 Lt C I\<close> nlt by blast
      have "\<not> Col I Y0 Z" 
        by (metis Col_cases Out_def \<open>C Out I Y0\<close> \<open>Y0 \<noteq> I\<close> \<open>\<not> Col I Z C\<close> 
            bet_col col_transitivity_1)
      have "Obtuse I Y0 Z" 
      proof (rule acute_bet__obtuse [where ?A="C"]) 
        show "Bet C Y0 I" 
          using l6_13_1 by (meson Lt_def \<open>C Out I Y0\<close> \<open>C Y0 Lt C I\<close> l6_6)
        show "I \<noteq> Y0" 
          using \<open>Y0 \<noteq> I\<close> by auto
        show "Acute C Y0 Z" 
          by (metis Out_def \<open>C Out I Y0\<close> \<open>Cong Z C C Y0\<close> \<open>\<not> Col I Y0 Z\<close> 
              col_trivial_2 cong_3421 cong__acute)
      qed
      hence "Per I Y0 Z \<or> Obtuse I Y0 Z"  
        by blast
      have "Y0 Z Lt I Z" 
        using l11_46 by (metis NCol_cases \<open>C Out I Y0\<close> \<open>Per I Y0 Z \<or> Obtuse I Y0 Z\<close> 
            \<open>Y0 \<noteq> I\<close> \<open>\<not> Col I Z C\<close> out_col)
      have "Y0 OutCircleS A B"
      proof -
        have "Z Y0 Le Z T" 
          by (metis Le_cases \<open>Cong I Z T Z\<close> \<open>Y0 Z Lt I Z\<close> cong__le 
              le_transitivity local.le_cases lt__nle)
        then obtain M where "Bet Z M T" and "Cong Z M Z Y0" 
          using le_bet by blast
        hence "T \<noteq> M" 
          by (metis Lt_def \<open>Cong I Z T Z\<close> \<open>Y0 Z Lt I Z\<close> cong_4312 cong_inner_transitivity)
        have "A B Lt A M" 
        proof (rule cong2_lt__lt [where ?A="A" and ?B="T" and ?C="A" and ?D="M"])
          show "A T Lt A M" 
            by (meson \<open>Bet A T Z\<close> \<open>Bet Z M T\<close> \<open>T \<noteq> M\<close> bet__lt1213 
                between_inner_transitivity between_symmetry)
          show "Cong A T A B" 
            using OnCircle_def \<open>T OnCircle A B\<close> by auto
          show "Cong A M A M"     
            by (simp add: cong_reflexivity)
        qed
        moreover have "Z Out A M" 
          by (metis Col_def \<open>Bet A T Z\<close> \<open>Bet Z M T\<close> \<open>Cong Z M Z Y0\<close> 
              \<open>T = Z \<Longrightarrow> False\<close> \<open>\<not> Col I Y0 Z\<close> bet_out bet_out_1 between_trivial2
              cong_reverse_identity l6_6 l6_7)
        hence "A M Le A Y0" 
          using \<open>Cong Z M Z Y0\<close> not_cong_3412 triangle_reverse_inequality by blast
        ultimately show ?thesis 
          using OutCircleS_def le3456_lt__lt by blast
      qed
      have "Y0 InAngle P C Z"
      proof -
        have "Z C Y0 LeA Z C P"    
        proof -
          have "Cong C P C Y0" 
            using \<open>P OnCircle C D\<close> \<open>Y0 OnCircle C D\<close> onc2__cong by auto
          moreover have "Cong C Z C Z" 
            by (simp add: cong_reflexivity)
          moreover have "T Z Le P Z" 
          proof -
            have "A P Le A T" 
              by (meson OutCircle_def \<open>P InCircleS A B\<close> \<open>T OnCircle A B\<close> 
                  cong__le le_transitivity local.le_cases onc212 onc2__cong outc__nincs_1)
            then obtain M where "Bet A M T" and "Cong A M A P" 
              using le_bet by blast
            have "Bet A M Z" 
              using \<open>Bet A M T\<close> \<open>Bet A T Z\<close> between_exchange4 by blast
            show ?thesis
            proof (cases "M = A")
              case True
              thus ?thesis 
                by (metis \<open>Bet A T Z\<close> \<open>Cong A M A P\<close> cong_diff_3 l5_12_a)
            next
              case False
              have "T Z Le M Z" 
                using \<open>Bet A M T\<close> \<open>Bet A T Z\<close> bet__le2313 between_exchange3 by blast
              moreover have "A Out Z M" 
                using False \<open>Bet A M Z\<close> bet_out l6_6 by presburger
              hence "M Z Le P Z" 
                using \<open>Cong A M A P\<close> cong_symmetry le_comm triangle_reverse_inequality by blast
              ultimately show ?thesis 
                using le_transitivity by blast
            qed
          qed
          hence "I Z Le P Z" 
            using \<open>Cong I Z T Z\<close> cong__le le_transitivity by blast
          hence "Y0 Z Lt P Z" 
            using \<open>Y0 Z Lt I Z\<close> le3456_lt__lt by blast
          ultimately show ?thesis 
            by (metis Out_def \<open>C Out I Y0\<close> \<open>C Out P X0\<close> \<open>C Out R Z\<close> 
                nlea__lta not_and_lt not_cong_3412 t18_18)
        qed
        moreover have "C R OS P Y0" 
          using \<open>C Out I Y0\<close> \<open>C R OS I P\<close> not_col_distincts one_side_symmetry 
            os_out_os by blast
        hence "Z C OS P Y0" 
          by (metis Out_def \<open>C Out R Z\<close> col_one_side invert_one_side out_col)
        ultimately show ?thesis
          using l11_24 lea_in_angle by blast
      qed
      hence "Y0 InAngle P C R" 
        using \<open>C Out R Z\<close> in_angle_trans inangle_distincts out341__inangle by blast
      obtain Y where "Bet P Y R" and "Y = C \<or> C Out Y Y0" 
        using InAngle_def \<open>Y0 InAngle P C R\<close> by blast
      have "Bet P R Y"
      proof -
        have "Bet P P Q" 
          by (simp add: \<open>Bet P P Q\<close>)
        moreover have "\<exists> X0.(X0 OnCircle C D \<and> C Out P X0 \<and> X0 InCircle A B)" 
          using \<open>\<exists>X0. X0 OnCircle C D \<and> C Out P X0 \<and> X0 InCircle A B\<close> by blast
        moreover have "Bet P Y Q" 
          using \<open>Bet P R Q\<close> \<open>Bet P Y R\<close> between_exchange4 by blast
        moreover have "\<exists> Y1.(Y1 OnCircle C D \<and> C Out Y Y1 \<and> Y1 OutCircle A B)" 
          using Col_def \<open>Col P Q C \<Longrightarrow> False\<close> \<open>Y = C \<or> C Out Y Y0\<close> 
            \<open>Y0 OnCircle C D\<close> \<open>Y0 OutCircleS A B\<close> between_symmetry calculation(3) 
            outcs__outc by blast
        ultimately show ?thesis
          using \<open>\<forall>X Y. Bet P X Q \<and> (\<exists>X0. X0 OnCircle C D \<and> C Out X X0 \<and> X0 InCircle A B ) \<and> 
                       Bet P Y Q \<and> (\<exists>Y0. Y0 OnCircle C D \<and> C Out Y Y0 \<and> Y0 OutCircle A B ) 
                       \<longrightarrow> Bet X R Y\<close> by presburger
      qed
      hence "Y = R" 
        using \<open>Bet P Y R\<close> between_equality_2 by auto
      hence False 
        by (metis \<open>C Out I Y0\<close> \<open>C R OS I P\<close> \<open>Y = C \<or> C Out Y Y0\<close> col123__nos 
            not_col_distincts os_out_os out_col)
    }
    ultimately have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D"  
      using \<open>Z OnCircle C D\<close> circle_cases by blast
  }
  thus ?thesis
    using circle_circle_aux by blast
qed

subsubsection "Dedekind cantor"

lemma nested__diff0:
  assumes "Nested A B" 
  shows "\<forall> n An Bn. A n An \<and> B n Bn \<longrightarrow> An \<noteq> Bn" 
proof -
  have "(\<forall> n. (\<exists> An Bn. A n An \<and> B n Bn)) \<and> (\<forall> n An Am Bm Bn. 
              (A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn) 
              \<longrightarrow> (Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm))" 
    using assms Nested_def by simp
  {
    fix n 
    have "\<forall> An Bn. A n An \<and> B n Bn \<longrightarrow> An \<noteq> Bn" 
    proof (induction n)
      case 0
      thus ?case 
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
               (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                   \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> 
          between_equality between_symmetry by blast
    next
      case (Suc n)
      thus ?case 
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
                    (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                    \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> by blast
    qed
  }
  thus ?thesis by blast
qed

lemma nested_sym: 
  assumes "Nested A B" 
  shows "Nested B A" 
proof -
  have "(\<forall> n. (\<exists> An Bn. A n An \<and> B n Bn)) \<and> (\<forall> n An Am Bm Bn.
    (A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn) 
    \<longrightarrow> (Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm))" 
    using assms Nested_def by simp
  hence "(\<forall> n. (\<exists> An Bn. B n An \<and> A n Bn))" 
    by simp
  moreover {
    fix n
    have "(\<forall>An Am Bm Bn.
    (B n An \<and> B (Suc n) Am \<and> A (Suc n) Bm \<and> A n Bn) \<longrightarrow>
    (Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm))" 
      using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
             (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                 \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> between_symmetry by blast
  }
  ultimately show ?thesis 
    using Nested_def by presburger
qed

lemma nested__ex_left: 
  assumes "Nested A B" 
  shows "\<exists> An. A n An" 
  using Nested_def assms by presburger

lemma nested__ex_right: 
  assumes "Nested A B" 
  shows "\<exists> Bn. B n Bn" 
  using assms nested__ex_left nested_sym by blast

lemma nested_aux1_1:
  fixes n::nat
  assumes "Nested A B" 
  shows "\<forall> Am Bm. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<longrightarrow> Bet An Am Bm" 
proof -
  have "(\<forall> n. (\<exists> An Bn. A n An \<and> B n Bn)) \<and>
 (\<forall> n An Am Bm Bn.
    (A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn) 
\<longrightarrow>
(Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm))" 
    using assms Nested_def by auto
  thus ?thesis 
    by blast
qed

lemma nested_aux1_2:
  fixes n::nat
  assumes "Nested A B" 
  shows "(n < m \<and> (Suc n) \<le> m) \<longrightarrow> ((\<forall> Am Bm. A n An \<and> A m Am \<and> B m Bm \<longrightarrow> Bet An Am Bm))" 
proof (induction m)
  show "(n < 0 \<and> Suc n \<le> 0) \<longrightarrow> ((\<forall>Am Bm. A n An \<and> A 0 Am \<and> B 0 Bm \<longrightarrow> Bet An Am Bm))"
    by simp    
  { 
    fix m 
    assume "(n < m \<and> Suc n \<le> m) \<longrightarrow> (\<forall>Am Bm. A n An \<and> A m Am \<and> B m Bm \<longrightarrow> Bet An Am Bm)" 
    {
      assume "n < Suc m \<and> Suc n \<le> Suc m" 
      hence "Suc n = Suc m \<or> Suc n \<le> m" 
        using le_Suc_eq by blast
      hence "n = m \<or> Suc n \<le> m" 
        by simp
      moreover
      have "n = m \<longrightarrow> (Suc n \<le> Suc m \<longrightarrow> 
                       (\<forall>Am Bm. A n An \<and> A (Suc m) Am \<and> B (Suc m) Bm \<longrightarrow> Bet An Am Bm))" 
        using assms nested_aux1_1 by blast
      moreover {
        fix Am' Bm'
        assume "Suc n \<le> m" and "A n An" and "A (Suc m) Am'" and "B (Suc m) Bm'" 
        obtain Am Bm where "A m Am" and "B m Bm" 
          using assms(1) Nested_def by fastforce
        hence "Bet An Am Bm" 
          using Suc_le_eq \<open>A n An\<close> \<open>Suc n \<le> m\<close> 
            \<open>n < m \<and> Suc n \<le> m \<longrightarrow> (\<forall>Am Bm. A n An \<and> A m Am \<and> B m Bm \<longrightarrow> Bet An Am Bm)\<close> 
          by blast
        have "Bet Am Am' Bm' \<and> Bet Am' Bm' Bm \<and> Am' \<noteq> Bm'" 
          using Nested_def \<open>A (Suc m) Am'\<close> \<open>A m Am\<close> \<open>B (Suc m) Bm'\<close> \<open>B m Bm\<close> assms by presburger
        hence "Bet An Am Bm'" 
          by (meson \<open>Bet An Am Bm\<close> bet_out_1 bet_out__bet between_inner_transitivity)
        hence "Bet An Am' Bm'"
          using \<open>Bet Am Am' Bm' \<and> Bet Am' Bm' Bm \<and> Am' \<noteq> Bm'\<close> between_exchange2 by blast
      }
      ultimately have "(n < Suc m \<and> (Suc n \<le> Suc m)) 
                        \<longrightarrow> (\<forall>Am Bm. A n An \<and> A (Suc m) Am \<and> B (Suc m) Bm \<longrightarrow> Bet An Am Bm)" 
        by blast
    }
  }
  thus "\<And>m. ((n < m \<and> Suc n \<le> m) \<longrightarrow> (\<forall>Am Bm. A n An \<and> A m Am \<and> B m Bm \<longrightarrow> Bet An Am Bm)) \<Longrightarrow>
         ((n < Suc m) \<and> Suc n \<le> Suc m) \<longrightarrow> 
          (\<forall>Am Bm. A n An \<and> A (Suc m) Am \<and> B (Suc m) Bm \<longrightarrow> Bet An Am Bm)" 
    by blast
qed

lemma nested_aux1:
  fixes n::nat
  assumes "Nested A B" and 
    "n < m" 
  shows "\<forall> Am Bm. A n An \<and> A m Am \<and> B m Bm \<longrightarrow> Bet An Am Bm" 
proof -
  have "m = (Suc n) \<or> (Suc n) \<le> m" 
    using less_eq_Suc_le assms(2) by blast 
  moreover have "(m = Suc n) \<longrightarrow> ?thesis"
    using nested_aux1_1 assms(2) assms(1) by blast
  moreover 
  {
    fix Am Bm
    assume "(Suc n) \<le> m" and "A n An" and "A m Am" and "B m Bm"
    hence "Bet An Am Bm" 
      using assms(1) nested_aux1_2 assms(2) by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma nested_aux2:
  assumes "Nested A B" and
    "n < m" and
    "A n An" and
    "A m Am" and
    "B n Bn"
  shows "Bet An Am Bn" 
proof -
  obtain Bm where "B m Bm" 
    using assms(1) nested__ex_right by blast
  have "Bet An Am Bm" 
    using \<open>A m Am\<close> \<open>A n An\<close> \<open>B m Bm\<close> assms(1) assms(2) nested_aux1 by blast
  moreover have "Bet Am Bm Bn" 
    using \<open>A m Am\<close> \<open>B m Bm\<close> \<open>B n Bn\<close> assms(1) assms(2) 
      between_symmetry nested_aux1 nested_sym by blast
  moreover have "Am \<noteq> Bm" 
    using \<open>A m Am\<close> \<open>B m Bm\<close> assms(1) nested__diff0 by auto
  ultimately show ?thesis 
    using outer_transitivity_between by blast
qed

lemma nested__bet:
  assumes "Nested A B" and 
    "n < n1" and
    "A n An" and
    "A n1 An1" and
    "B m Bm"
  shows "Bet An An1 Bm" 
proof -
  have "Nested B A" 
    using assms(1) nested_sym by blast
  have "n1 = m \<longrightarrow> Bet An An1 Bm" 
    using nested_aux1 assms(1) assms(2) assms(3) assms(4) assms(5) by blast
  moreover {
    assume "n1 \<noteq> m"
    obtain Bn1 where "B n1 Bn1" 
      using \<open>Nested B A\<close> nested__ex_left by blast
    have "Bet An An1 Bn1" 
      using \<open>B n1 Bn1\<close> assms(1) assms(2) assms(3) assms(4) nested_aux1 by blast
    {
      assume "n1 < m" 
      have "Bet Bn1 Bm An1" 
        using nested_aux2 [where ?A="B" and ?B="A" and ?n="n1" and ?m="m"]
          \<open>Nested B A\<close> \<open>n1 < m\<close> \<open>B n1 Bn1\<close>assms(5) assms(4) by blast
      hence "Bet An1 Bm Bn1" 
        using Bet_cases by presburger
      hence "Bet An An1 Bm" 
        using \<open>Bet An An1 Bn1\<close> between_inner_transitivity by blast
    }
    moreover {
      assume "m < n1"
      have "An1 \<noteq> Bn1" 
        using \<open>B n1 Bn1\<close> assms(1) assms(4) nested__diff0 by auto
      moreover have "Bet An1 Bn1 Bm" 
        using \<open>B n1 Bn1\<close> \<open>Nested B A\<close> \<open>m < n1\<close> assms(4) assms(5) 
          between_symmetry nested_aux1 by blast
      ultimately have  "Bet An An1 Bm" 
        using \<open>Bet An An1 Bn1\<close> outer_transitivity_between by blast
    }
    ultimately have "Bet An An1 Bm" 
      using \<open>n1 \<noteq> m\<close> linorder_neqE_nat by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma nested__diff:
  assumes "Nested A B" and
    "A n An" and 
    "B m Bm" 
  shows "An \<noteq> Bm" 
proof -
  have "n = m \<longrightarrow> ?thesis" 
    using assms(1) assms(2) assms(3) nested__diff0 by blast
  moreover {
    assume "n < m" 
    obtain Am where "A m Am" 
      using Nested_def assms(1) by presburger
    hence "Bet An Am Bm" 
      using \<open>n < m\<close> assms(1) assms(2) assms(3) nested_aux1 by blast
    hence ?thesis 
      using \<open>A m Am\<close> assms(1) assms(3) bet_neq12__neq nested__diff0 by blast
  }
  moreover {
    assume "m < n"
    obtain Bn where "B n Bn" 
      using Nested_def assms(1) by presburger
    have "Nested B A" 
      by (simp add: assms(1) nested_sym)
    hence "Bet Bm Bn An" 
      using \<open>B n Bn\<close> \<open>m < n\<close> assms(2) assms(3) nested__bet by blast
    hence ?thesis 
      using \<open>B n Bn\<close> assms(1) assms(2) bet_neq12__neq nested__diff0 by blast
  }
  ultimately show ?thesis 
    using nat_neq_iff by blast
qed

lemma dedekind__cantor:
  assumes "DedekindsAxiom"
  shows "CantorsAxiom" 
proof -
  {
    fix A B
    assume "Nested A B"
    obtain A0 where "A 0 A0" 
      using Nested_def \<open>Nested A B\<close> by presburger
    hence "\<forall> X Y. (\<exists> n. 0 < n \<and> A n X) \<and> (\<exists> m. B m Y) \<longrightarrow> Bet A0 X Y" 
      using \<open>Nested A B\<close> nested__bet by blast
    hence "\<exists> A0. \<forall> X Y. (\<exists> n. 0 < n \<and> A n X) \<and> (\<exists> m. B m Y) \<longrightarrow> Bet A0 X Y" 
      by blast
    hence "\<exists> X. \<forall> An Bm. (\<exists> n. 0 < n \<and> A n An) \<and> (\<exists> m. B m Bm) \<longrightarrow> Bet An X Bm" 
      using assms DedekindsAxiom_def by simp
    then obtain X where "\<forall> An Bm. (\<exists> n. 0 < n \<and> A n An) \<and> (\<exists> m. B m Bm) \<longrightarrow> Bet An X Bm" 
      by blast
    {
      fix n An Bn
      assume "A n An" and "B n Bn" 
      have "0 < n \<longrightarrow> Bet An X Bn" 
        using \<open>A n An\<close> \<open>B n Bn\<close> 
          \<open>\<forall>An Bm. (\<exists>n>0. A n An) \<and> (\<exists>m. B m Bm) \<longrightarrow> Bet An X Bm\<close> by auto
      moreover 
      { 
        assume "n = 0" 
        obtain A1 where "A 1 A1" 
          using nested__ex_left \<open>Nested A B\<close> by blast
        hence "Bet An A1 Bn" 
          using \<open>A n An\<close> \<open>B n Bn\<close> \<open>Nested A B\<close> \<open>n = 0\<close> nested_aux2 by blast
        hence "Bet An X Bn" 
          using \<open>A 1 A1\<close> \<open>B n Bn\<close> between_exchange2
            \<open>\<forall>An Bm. (\<exists>n>0. A n An) \<and> (\<exists>m. B m Bm) \<longrightarrow> Bet An X Bm\<close> by blast
      }
      ultimately have "Bet An X Bn" 
        by blast
    }
    hence "\<exists> X. \<forall> n An Bn. (A n An \<and> B n Bn) \<longrightarrow> Bet An X Bn" 
      by blast
  }
  thus ?thesis 
    using CantorsAxiom_def by blast
qed

end
end

