(* IsageoCoq2_R1

Tarski_Continuity.thy
TODO
[ ] all def
[ ] all prop
[ ] move Require Export GeoCoq.Tarski_dev.Ch12_parallel.

Version 2.2.0 IsaGeoCoq2_R1, Port part of GeoCoq 3.4.0
Version 2.1.0 IsaGeoCoq2_R1, Port part of GeoCoq 3.4.0
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
theory Tarski_Continuity

imports
  Tarski_Neutral

begin

(*>*)

context Tarski_neutral_dimensionless
begin

section "Circle"

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

subsubsection "Circle"

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

(** Given two points U and V on a circle, the points of the line UV which are inside the circle are
    between U and V. *) 

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

(** Given two points U and V on a circle, all points of line UV which are outside the segment UV are
    outside the circle. *)

lemma onc2_out__outcs:
  assumes "U \<noteq> V" and
    "U OnCircle A B" and
    "V OnCircle A B" and
    "P Out U V"
  shows "P OutCircleS A B" 
  by (meson Col_cases assms(1) assms(2) assms(3) assms(4) 
      col_inc_onc2__bet not_bet_and_out out_col outcs__ninc_2)

(** Given two points U and V inside a circle, all points of line UV which are outside the circle are
    outside the segment UV. *)

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

(** Given a circle of center O and a ray OX, there is a point on the ray which is also on the circle. *)

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

(** The line from the center of a circle to the midpoint of a chord is perpendicular to the chord. *)

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
end
(*context Tarski2D
begin

end
end
  (*


Context `{T2D:Tarski_2D}.

(** The center of a circle belongs to the perpendicular bisector of each chord *)

lemma mid_onc2_perp__col:
assumes "A \<noteq> B" and
"A OnCircle PO P" and
"B OnCircle PO P" and
"X Midpoint A B" and
"X Y Perp A B" 
shows "Col X Y PO" sorry

(** Euclid Book III Prop 4.
 If in a circle two straight lines which do not pass through the center cut one another,
 then they do not bisect one another.
 *)

lemma mid2_onc4__eq: 
assumes "B \<noteq> C" and 
"A \<noteq> B" and
 "OnCircle A PO P" and
 "OnCircle B PO P" and
 "OnCircle C PO P" and
 "OnCircle D PO P" and
 "Midpoint X A C" and
 "Midpoint X B D" and
 shows "X = PO" sorry

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle,
 then the point taken is the center of the circle.
*)

lemma cong2_onc3__eq: 
assumes "A \<noteq> B" and
"A \<noteq> C" and
"B \<noteq> C" and
"A OnCircle PO P" and
"B OnCircle PO P" and
"C OnCircle PO P" and
"Cong X A X B" and
"Cong X A X C"
shows "X = PO" sorry

Lemma onc2_mid_cong_col : forall O P U V M X,
 U \<noteq> V ->OnCircle U O P -> OnCircle V O P -> Midpoint M U V -> Cong U X V X -> Col O X M.


Lemma cong_onc3_cases : forall O P A X Y,
 Cong A X A Y ->
 OnCircle A O P -> OnCircle X O P -> OnCircle Y O P ->
 X = Y \/ ReflectL X Y O A.

Lemma bet_cong_onc3_cases : forall O P A X Y T,
 T \<noteq> O -> Bet A O T -> Cong T X T Y ->
 OnCircle A O P  -> OnCircle X O P  -> OnCircle Y O P ->
 X = Y \/ ReflectL X Y O A.

Lemma prop_7_8 : forall O P A B T X Y , Diam A B O P -> Bet A O T 
                               -> OnCircle X O P -> OnCircle Y O P
                               -> LeA A O X A O Y -> Le T Y T X.




Lemma Prop_7_8_uniqueness : forall O P A X Y Z T, T \<noteq> O -> X \<noteq> Y ->
  Bet A O T -> Cong T X T Y -> Cong T X T Z ->
  OnCircle A O P -> OnCircle X O P -> OnCircle Y O P -> OnCircle Z O P ->
  Z = X \/ Z = Y.

Lemma chords_midpoints_col_par : forall O P A M B C N D, 
 O \<noteq> P ->
 OnCircle A O P -> OnCircle B O P ->
 OnCircle C O P -> OnCircle D O P ->
 Midpoint M A B -> Midpoint N C D ->
 Col O M N -> \<not> Col O A B -> \<not> Col O C D -> Par A B C D.

Lemma onc3_mid2__ncol : forall O P A B C A' B',
 O \<noteq> P -> 
 OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
 Midpoint A' A C -> Midpoint B' B C -> \<not> Col A B C ->
 \<not> Col O A' B' \/ A' = O \/ B' = O.

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle, 
 then the point taken is the center of the circle.*)

Lemma onc4_cong2__eq: 
 forall A B C D O P X,
 A\<noteq>B -> C\<noteq>D ->
 \<not> Par A B C D ->
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Cong A X B X ->
 Cong C X D X ->
 O=X.

*)
*)