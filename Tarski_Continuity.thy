(* IsageoCoq2_R1

Tarski_Continuity.thy
TODO
[ ] Completeness: tout revoir : f entre 2 espaces différents
[ ] all def
[ ] all prop
[ ] move Require Export GeoCoq.Tarski_dev.Ch12_parallel.
[ ] move part circle with Tarski2D

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
theory Tarski_Continuity

imports
  HOL.Orderings
  Tarski_Neutral
  Tarski_Archimedes
  Tarski_2D (*peut-être faire 2 fichiers ?*)
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

context Tarski_2D

begin

(** The center of a circle belongs to the perpendicular bisector of each chord *)

lemma mid_onc2_perp__col:
  assumes "A \<noteq> B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "X Midpoint A B" and
    "X Y Perp A B" 
  shows "Col X Y PO"
  using all_coplanar assms(1) assms(2) assms(3) assms(4) assms(5) 
    cop_mid_onc2_perp__col by blast

(** Euclid Book III Prop 4.
 If in a circle two straight lines which do not pass through the center cut one another,
 then they do not bisect one another.
 *)

lemma mid2_onc4__eq: 
  assumes "B \<noteq> C" and 
    "A \<noteq> B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "D OnCircle PO P" and
    "X Midpoint A C" and
    "X Midpoint B D" 
  shows "X = PO" 
proof -
  have "Per PO X A" 
    using assms(3) assms(5) assms(7) mid_onc2__per by blast
  have "Per PO X B" 
    using assms(4) assms(6) assms(8) mid_onc2__per by auto
  {
    assume "X \<noteq> PO"
    have "Col A B X" 
      by (meson Per_cases \<open>Per PO X A\<close> \<open>Per PO X B\<close> \<open>X \<noteq> PO\<close> per2__col)
    have "Col B X D" 
      using Col_def Midpoint_def assms(8) by blast
    have "Col A X C" 
      by (simp add: assms(7) bet_col midpoint_bet)
    have "A = X \<longrightarrow> False" 
      by (metis \<open>Per PO X B\<close> assms(2) assms(3) assms(4) 
          col_trivial_3 is_midpoint_id_2 onc2_per__mid)
    moreover have "A \<noteq> X \<longrightarrow> False" 
      by (metis \<open>Col A B X\<close> \<open>Col A X C\<close> assms(1) assms(2) assms(3) 
          assms(4) assms(5) assms(7) col_trivial_3 colx 
          line_circle_two_points midpoint_distinct_2)
    ultimately have False 
      by blast
  }
  thus ?thesis
    by auto
qed

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
  shows "X = PO"
proof -
  have "Coplanar A B C PO" 
    using all_coplanar by simp
  moreover have "Coplanar A B C X" 
    using all_coplanar by simp
  ultimately show ?thesis 
    using assms(1) assms(2) assms(3) assms(4) assms(5) 
      assms(6) assms(7) assms(8) cong2_cop2_onc3__eq by blast
qed

lemma onc2_mid_cong_col:
  assumes "U \<noteq> V" and 
    "U OnCircle PO P" and
    "V OnCircle PO P" and
    "M Midpoint U V" and
    "Cong U X V X"
  shows "Col PO X M" 
  by (meson Col_def Cong_cases assms(1) assms(2) assms(3) assms(4) 
      assms(5) midpoint_cong onc2__cong upper_dim)

lemma cong_onc3_cases:
  assumes "Cong A X A Y" and
    "A OnCircle PO P" and
    "X OnCircle PO P" and
    "Y OnCircle PO P" 
  shows " X = Y \<or> X Y ReflectL PO A" 
proof (cases "X = Y")
  case True
  thus ?thesis 
    by blast
next
  case False
  hence "X \<noteq> Y" 
    by simp
  obtain M where "M Midpoint X Y" 
    using midpoint_existence by blast
  hence "Per PO M X" 
    using assms(3) assms(4) mid_onc2__per by blast
  have "Per A M X" 
    using Per_def \<open>M Midpoint X Y\<close> assms(1) by auto
  have "M \<noteq> X" 
    using False \<open>M Midpoint X Y\<close> is_midpoint_id by force
  hence "Col A PO M" 
    using \<open>Per A M X\<close> \<open>Per PO M X\<close> per2__col by auto
  have "M Midpoint Y X" 
    using Mid_cases \<open>M Midpoint X Y\<close> by blast
  moreover have "Col PO A M" 
    using \<open>Col A PO M\<close> col_permutation_4 by blast
  moreover have "PO A Perp Y X" 
  proof (cases "M = PO")
    case True
    thus ?thesis           
      by (metis False OnCircle_def assms(1) assms(2) assms(3) 
          calculation(1) cong_diff_3 cong_reflexivity 
          mid_onc2__perp onc2__cong perp_left_comm)
  next
    case False
    then show ?thesis 
      by (metis \<open>M Midpoint X Y\<close> \<open>X \<noteq> Y\<close> assms(2) assms(3) 
          assms(4) calculation(2) col_permutation_5 cong_diff 
          mid_onc2__perp onc2__cong perp_col perp_right_comm)
  qed
  ultimately show ?thesis 
    using ReflectL_def by blast
qed

lemma bet_cong_onc3_cases:
  assumes "T \<noteq> PO" and 
    "Bet A PO T"  and 
    "Cong T X T Y" and
    "A OnCircle PO P" and
    "X OnCircle PO P" and
    "Y OnCircle PO P"  
  shows "X = Y \<or> X Y ReflectL PO A" 
  using Col_cases assms(1) assms(2) assms(3) assms(4) assms(5) 
    assms(6) bet_col cong_onc3_cases l4_17 onc2__cong by blast

lemma prop_7_8: 
  assumes "Diam A B PO P" and
    "Bet A PO T" and
    "X OnCircle PO P" and
    "Y OnCircle PO P" and
    "A PO X LeA A PO Y"
  shows "T Y Le T X" 
proof (cases "PO = P")
  case True
  thus ?thesis 
    by (metis assms(4) assms(5) lea_distincts onc_not_center onc_sym)
next
  case False
  hence "PO \<noteq> P" 
    by simp
  show ?thesis 
  proof (cases "PO = T")
    case True 
    thus ?thesis 
      using assms(3) assms(4) cong__le onc2__cong by auto
  next
    case False
    hence "PO \<noteq> T"
      by simp

    show ?thesis 
    proof (cases "Cong A X A Y")
      case True
      thus ?thesis 
        by (metis assms(2) assms(3) assms(4) assms(5) bet_col 
            cong__le l4_17 lea_distincts not_cong_3412 onc2__cong)
    next
      case False
      have "T X Le T A" 
        using assms(1) assms(2) assms(3) bet_onc_le_b by auto
      have "Y PO T LeA X PO T" 
        by (metis \<open>PO \<noteq> T\<close> assms(2) assms(5) l11_36_aux1 lea_comm lea_distincts)
      have "Cong PO X PO Y" 
        using assms(3) assms(4) onc2__cong by blast 
      thus ?thesis 
        using t18_18 by (metis \<open>PO \<noteq> T\<close> \<open>Y PO T LeA X PO T\<close> cong_identity 
            cong_reflexivity le_reflexivity lta__nlea nlt__le not_cong_3412 t18_19)
    qed
  qed
qed

lemma Prop_7_8_uniqueness: 
  assumes "T \<noteq> PO" and
    "X \<noteq> Y" and
    (*  "Bet A PO T" and*)
    "Cong T X T Y" and
    "Cong T X T Z" and
    (* "A OnCircle PO P" and *)
    "X OnCircle PO P" and
    "Y OnCircle PO P" and
    "Z OnCircle PO P" 
  shows "Z = X \<or> Z = Y" 
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) cong2_onc3__eq)

lemma chords_midpoints_col_par:
  assumes (*"PO \<noteq> P" and*)
    "A OnCircle PO P" and
    "B OnCircle PO P" and 
    "C OnCircle PO P" and
    "D OnCircle PO P" and 
    "M Midpoint A B" and
    "N Midpoint C D" and
    "Col PO M N" and 
    "\<not> Col PO A B" and 
    "\<not> Col PO C D" 
  shows "A B Par C D" 
proof -
  have "PO M Perp A B"
    by (metis assms(1) assms(2) assms(5) assms(8) mid_onc2__perp midpoint_col not_col_distincts)
  moreover have "PO N Perp C D" 
    by (metis assms(9) assms(3) assms(4) assms(6) mid_onc2__perp midpoint_col not_col_distincts)
  hence "PO M Perp C D" 
    by (metis assms(5) assms(8) assms(7) col_permutation_5 midpoint_col perp_col)
  ultimately show ?thesis 
    by (meson Perp_cases l12_9_2D)
qed

lemma onc3_mid2__ncol:
  assumes (*"PO \<noteq> P" and*) 
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and 
    "A' Midpoint A C" and
    "B' Midpoint B C" and
    "\<not> Col A B C"
  shows "\<not> Col PO A' B' \<or> A' = PO \<or> B' = PO" 
proof (cases "Col PO A C")
  case True
  hence "A = C \<or> PO Midpoint A C" 
    using assms(1) assms(3) l7_20 not_col_permutation_4 onc2__cong by blast 
  thus ?thesis   
    using MidR_uniq_aux assms(4) assms(6) col_trivial_3 by blast
next
  case False
  hence "\<not> Col PO A C"
    by simp
  show ?thesis 
  proof (cases "Col PO B C")
    case True
    hence "B = C \<or> PO Midpoint B C" 
      by (metis assms(2) assms(3) col_permutation_4 l7_20_bis onc2__cong)
    thus ?thesis 
      using assms(5) assms(6) col_trivial_2 l7_17 by blast
  next
    case False
    hence "\<not> Col PO B C"
      by simp
    {
      assume "Col PO A' B'"
      hence "A C Par B C" 
        using False \<open>\<not> Col PO A C\<close> assms(2) assms(3) assms(4) 
          assms(5) assms(1) chords_midpoints_col_par by force
      hence False 
        using assms(6) par_comm par_id_2 by blast
    }
    thus ?thesis 
      by blast
  qed
qed

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle, 
 then the point taken is the center of the circle.*)

lemma onc4_cong2__eq: 
  assumes "A \<noteq> B" and
    "C \<noteq> D" and
    "\<not> A B Par C D" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "D OnCircle PO P" and
    "Cong A X B X" and
    "Cong C X D X" 
  shows "PO = X" 
proof (cases "PO = P")
  case True
  then show ?thesis   
    using assms(2) assms(6) assms(7) inc_eq onc__inc by blast
next
  case False
  obtain M where "M Midpoint A B" 
    using midpoint_existence by blast
  hence "Col PO X M" 
    using assms(1) assms(4) assms(5) assms(8) onc2_mid_cong_col by blast
  obtain N where "N Midpoint C D" 
    using midpoint_existence by blast
  hence "Col PO X N" 
    using assms(2) assms(6) assms(7) assms(9) onc2_mid_cong_col by blast
  show ?thesis 
  proof (cases "PO = X")
    case True
    thus ?thesis 
      by simp
  next
    case False
    hence "PO \<noteq> X"
      by simp
    have "Col PO M N" 
      using False \<open>Col PO X M\<close> \<open>Col PO X N\<close> col_transitivity_1 by blast
    have "X = M \<or> \<not> Col A B X \<and> M PerpAt X M A B" 
      by (simp add: \<open>M Midpoint A B\<close> assms(1) assms(8) cong_perp_or_mid)
    moreover have "X = N \<or> \<not> Col C D X \<and> N PerpAt X N C D" 
      using \<open>N Midpoint C D\<close> assms(2) assms(9) cong_perp_or_mid by auto
    moreover 
    {
      assume "X = M" and "X = N"
      hence "PO = X" 
        by (metis \<open>M Midpoint A B\<close> \<open>N Midpoint C D\<close> assms(1) assms(3) 
            assms(4) assms(5) assms(6) assms(7) l12_17 mid2_onc4__eq 
            par_reflexivity symmetric_point_uniqueness)
    }
    moreover 
    {
      assume "X = M" and "\<not> Col C D X" and "N PerpAt X N C D" 
      hence "M N Perp C D" 
        using perp_in_perp by blast

      have "PO = X" 
      proof (cases "Col PO A B")
        case True
        thus ?thesis 
          by (metis \<open>M Midpoint A B\<close> \<open>X = M\<close> assms(1) assms(4) assms(5) 
              assms(8) col_onc2__mid cong_perp_or_mid midpoint_col not_col_permutation_2)
      next
        case False
        have "PO M Perp A B" 
          using \<open>M Midpoint A B\<close> \<open>PO \<noteq> X\<close> \<open>X = M\<close> assms(1) assms(4) 
            assms(5) mid_onc2__perp by blast
        hence "M PO Perp C D" 
          by (metis Perp_cases \<open>Col PO M N\<close> \<open>Col PO X M\<close> \<open>M N Perp C D\<close> 
              \<open>X = M\<close> assms(3) calculation(3) l12_9_2D perp_col0)
        then show ?thesis 
          by (meson Perp_cases \<open>PO M Perp A B\<close> assms(3) l12_9_2D)
      qed
    }
    moreover 
    {
      assume "\<not> Col A B X" and "M PerpAt X M A B" and "X = N"

      have "PO = X" 
      proof (cases "Col PO C D")
        case True
        have "C = D \<or> PO Midpoint C D" 
          using Col_cases True assms(6) assms(7) col_onc2__mid by blast
        thus ?thesis 
          by (simp add: \<open>N Midpoint C D\<close> \<open>X = N\<close> assms(2) l7_17)
      next
        case False
        have "PO N Perp C D" 
          using \<open>N Midpoint C D\<close> \<open>PO \<noteq> X\<close> \<open>X = N\<close> assms(2) assms(6) assms(7) 
            mid_onc2__perp by auto
        have "N M Perp A B" 
          using \<open>M PerpAt X M A B\<close> \<open>X = N\<close> perp_in_perp by auto
        hence "A B Par C D" 
          by (metis Col_perm Perp_cases \<open>Col PO M N\<close> \<open>Col PO X N\<close> 
              \<open>PO N Perp C D\<close> \<open>X = N\<close> calculation(3) l12_9_2D perp_col0)
        thus ?thesis 
          by (simp add: assms(3))
      qed
    }
    moreover 
    {
      assume "\<not> Col A B X" and "M PerpAt X M A B" and
        "\<not> Col C D X" and "N PerpAt X N C D" 
      have "X M Perp A B" 
        using \<open>M PerpAt X M A B\<close> perp_in_perp by auto
      hence "X PO Perp A B" 
        by (metis Col_cases False \<open>Col PO X M\<close> perp_col)
      moreover have "X N Perp C D"
        using \<open>N PerpAt X N C D\<close> perp_in_perp by auto
      hence "X PO Perp C D" 
        by (metis False \<open>Col PO X N\<close> not_col_permutation_2 perp_col)
      ultimately have "PO = X" 
        by (meson Perp_cases assms(3) l12_9_2D)
    }
    ultimately show ?thesis 
      by blast
  qed
qed

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
        have "A B Lt A M" proof (rule cong2_lt__lt [where ?A="A" and ?B="T" and ?C="A" and ?D="M"])
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

subsubsection "Dedekind archimedes"

lemma archimedes_aux :
  assumes "\<forall> A B C. A Out B C \<longrightarrow> Reach A B A C" 
  shows "ArchimedesAxiom" 
proof -
  {
    fix A B C D::TPoint
    assume "A \<noteq> B" 
    have "Reach A B C D" 
    proof (cases "C = D")
      case True
      have "Grad A B B" 
        by (simp add: grad_equiv_coq_1)
      moreover have "C D Le A B" 
        by (simp add: True le_trivial)
      ultimately show ?thesis 
        using Reach_def by blast
    next
      case False
      hence "C \<noteq> D" 
        by simp
      obtain E where "A Out B E" and "Cong A E C D" 
        using False \<open>A \<noteq> B\<close> segment_construction_3 by blast
      obtain B' where "Grad A B B'" and "A E Le A B'" 
        using assms(1) Reach_def \<open>A Out B E\<close> by blast
      moreover have "C D Le A B'" 
        using \<open>Cong A E C D\<close> calculation(2) cong__le3412 le_transitivity by blast 
      ultimately show ?thesis 
        using Reach_def by blast
    qed
  }
  thus ?thesis 
    using archimedes_axiom_def by blast
qed

definition AlphaTmp :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  where
    "AlphaTmp A B \<equiv> \<lambda> X. X = A \<or> (A Out B X \<and> Reach A B A X)"

definition BetaTmp :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool"
  where
    "BetaTmp A B \<equiv> \<lambda> X. A Out B X \<and> \<not> Reach A B A X" 

lemma dedekind_variant__archimedes: 
  assumes "DedekindVariant" 
  shows "archimedes_axiom" 
proof -
  {
    fix A B C
    assume "A Out B C"
    {
      assume "\<not> Reach A B A C"
      have "\<exists> X. \<forall> P Q. (P = A \<or> (A Out B P \<and> Reach A B A P)) \<and> 
                        (A Out B Q \<and> \<not> Reach A B A Q) \<longrightarrow> Bet P X Q" 
      proof -
        let ?Alpha = "(AlphaTmp A B)"
        let ?Beta = "(BetaTmp A B)"
        have "\<forall> Alpha Beta. \<forall> A C. (Alpha A \<and> Beta C \<and> 
                (\<forall> P. A Out P C \<longrightarrow> (Alpha P \<or> Beta P)) \<and> (\<forall> X Y. (Alpha X \<and> Beta Y) 
                \<longrightarrow> (Bet A X Y \<and> X \<noteq> Y))) \<longrightarrow> (\<exists> B'. \<forall> X Y. (Alpha X \<and> Beta Y) 
                       \<longrightarrow> Bet X B' Y)"
          using assms DedekindVariant_def by auto
        hence 2: "\<forall> A C. (?Alpha A \<and> ?Beta C \<and> (\<forall> P. A Out P C \<longrightarrow> (?Alpha P \<or> ?Beta P)) \<and> 
                   (\<forall> X Y. (?Alpha X \<and> ?Beta Y) \<longrightarrow> (Bet A X Y \<and> X \<noteq> Y))) 
                   \<longrightarrow> (\<exists> B'. \<forall> X Y. (?Alpha X \<and> ?Beta Y) \<longrightarrow> Bet X B' Y)"
          by simp
        have "?Alpha A" 
          by (simp add: AlphaTmp_def)
        moreover have "?Beta C" 
          by (simp add: BetaTmp_def \<open>A Out B C\<close> \<open>\<not> Reach A B A C\<close>)
        moreover have "\<forall> P. A Out P C \<longrightarrow> (?Alpha P \<or> ?Beta P)" 
          by (meson AlphaTmp_def BetaTmp_def \<open>A Out B C\<close> l6_6 l6_7)
        moreover {
          fix P Q
          assume "?Alpha P" and "?Beta Q" 
          hence "P = A \<or> (A Out B P \<and> Reach A B A P)" 
            using AlphaTmp_def by metis
          have "A Out B Q \<and> \<not> Reach A B A Q"
            using BetaTmp_def \<open>BetaTmp A B Q\<close> by auto
          hence "A Out B Q"
            by simp
          have "\<not> Reach A B A Q"
            using \<open>A Out B Q \<and> \<not> Reach A B A Q\<close> by auto
          have "Bet A P Q \<and> P \<noteq> Q" 
          proof -
            have "P = A \<longrightarrow> ?thesis" 
              using Out_def \<open>A Out B Q \<and> \<not> Reach A B A Q\<close> between_trivial2 by auto
            moreover {
              assume  "A Out B P" and "Reach A B A P"
              have "A Out P Q" 
                using Out_cases \<open>A Out B P\<close> \<open>A Out B Q\<close> l6_7 by blast
              hence "Bet A P Q \<or> Bet A Q P" 
                by (simp add: Out_def)
              moreover {
                assume "Bet A Q P"
                obtain B' where "Grad A B B'" and "A P Le A B'" 
                  using Reach_def \<open>Reach A B A P\<close> by blast
                hence "A Q Le A B'" 
                  using \<open>Bet A Q P\<close> l5_12_a le_transitivity by blast
                hence "Reach A B A Q" 
                  using Reach_def \<open>Grad A B B'\<close> by blast
                hence False 
                  by (simp add: \<open>\<not> Reach A B A Q\<close>)
                hence "Bet A P Q" 
                  by blast
              }
              ultimately have "Bet A P Q" 
                by blast
              moreover have "P \<noteq> Q" 
                using \<open>Reach A B A P\<close> \<open>\<not> Reach A B A Q\<close> by auto
              ultimately have "Bet A P Q \<and> P \<noteq> Q" 
                by simp
            }
            ultimately show ?thesis 
              using \<open>P = A \<or> A Out B P \<and> Reach A B A P\<close> by fastforce
          qed
        }
        hence "\<exists> B'. \<forall> X Y. (?Alpha X \<and> ?Beta Y) \<longrightarrow> Bet X B' Y" 
          using 2 calculation(1) calculation(2) calculation(3) by blast
        thus ?thesis 
          using AlphaTmp_def BetaTmp_def by simp
      qed
      then obtain X where "\<forall> P Q. (P = A \<or> (A Out B P \<and> Reach A B A P)) \<and> 
                                  (A Out B Q \<and> \<not> Reach A B A Q) \<longrightarrow> Bet P X Q" 
        by blast
      have "A \<noteq> B" 
        using \<open>A Out B C\<close> out_diff1 by blast
      have "C \<noteq> A" 
        using Out_def \<open>A Out B C\<close> by presburger
      have "Grad A B B" 
        by (simp add: grad_equiv_coq_1)
      have "B = A \<or> A Out B B \<and> Reach A B A B"           
        using Reach_def bet__le2313 between_trivial2 grad_equiv_coq_1 out_trivial by blast
      hence "Bet B X C" 
        by (simp add: \<open>A Out B C\<close> \<open>\<not> Reach A B A C\<close> 
            \<open>\<forall>P Q. (P = A \<or> A Out B P \<and> Reach A B A P) \<and> A Out B Q \<and> \<not> Reach A B A Q 
                   \<longrightarrow> Bet P X Q\<close>)
      have "A Out B X" 
        using \<open>A Out B C\<close> \<open>Bet B X C\<close> out_bet_out_1 by blast
      have "Bet A B C \<or> Bet A C B" 
        using Out_def \<open>A Out B C\<close> by auto
      {
        assume "Bet A C B"
        have "A C Le A B" 
          by (simp add: \<open>Bet A C B\<close> bet__le1213)
        hence "Reach A B A C" 
          using Reach_def \<open>Grad A B B\<close> by blast
        hence False 
          using \<open>\<not> Reach A B A C\<close> by auto
      }
      hence "Bet A B C" 
        using \<open>Bet A B C \<or> Bet A C B\<close> by blast
      {
        assume "Reach A B A X" 
        then obtain X1 where "X Out C X1" and "Cong X X1 A B" 
          by (metis \<open>A \<noteq> B\<close> \<open>\<not> Reach A B A C\<close> segment_construction_3)
        have "Bet A X X1" 
          by (meson Bet_cases \<open>Bet A B C\<close> \<open>Bet B X C\<close> \<open>X Out C X1\<close> 
              bet_out__bet between_exchange4)
        have "X Out X1 C" 
          using Out_cases \<open>X Out C X1\<close> by blast
        moreover have "Bet X1 X C" 
        proof -
          have "A Out B X1" 
            by (metis \<open>A \<noteq> B\<close> \<open>Bet A B C\<close> \<open>Bet A X X1\<close> \<open>Bet B X C\<close> bet_out 
                between_exchange4 between_inner_transitivity)
          moreover 
          obtain B' where "Grad A B B'" and "A X Le A B'" 
            using Reach_def \<open>Reach A B A X\<close> by blast
          obtain B1' where "Bet A B' B1'" and "Cong B' B1' A B" 
            using segment_construction by blast
          hence "Grad A B B1'" 
            using \<open>Grad A B B'\<close> \<open>Grad A B B\<close> cong_symmetry grad_sum by blast
          moreover have "X X1 Le B' B1'" 
            by (meson \<open>Cong B' B1' A B\<close> \<open>Cong X X1 A B\<close> cong__le3412 
                cong_reflexivity cong_symmetry l5_6)
          hence "A X1 Le A B1'" 
            using \<open>A X Le A B'\<close> \<open>Bet A B' B1'\<close> \<open>Bet A X X1\<close> bet2_le2__le1346 by force
          ultimately have "Reach A B A X1" 
            using Reach_def by blast
          show ?thesis 
            using \<open>A Out B C\<close> \<open>\<not> Reach A B A C\<close> \<open>A Out B X1\<close> \<open>Reach A B A X1\<close>
              \<open>\<forall>P Q. (P = A \<or> A Out B P \<and> Reach A B A P) \<and> A Out B Q \<and> \<not> Reach A B A Q 
                     \<longrightarrow> Bet P X Q\<close> by blast
        qed
        ultimately have "Bet X1 X C \<and> X Out X1 C" 
          by simp
        hence False 
          using not_bet_and_out by blast
      }
      moreover 
      {
        assume "\<not> Reach A B A X" 
        have "X \<noteq> B" 
          using \<open>A \<noteq> B\<close> \<open>B = A \<or> A Out B B \<and> Reach A B A B\<close> calculation by blast
        have "X A Le A B \<longrightarrow> False"             
          by (meson \<open>Bet A B C\<close> \<open>Bet B X C\<close> \<open>X \<noteq> B\<close> bet_le_eq between_exchange3 
              between_symmetry le_right_comm)
        moreover 
        {
          assume "A B Le X A" 
          have "Bet A B X" 
            using \<open>Bet A B C\<close> \<open>Bet B X C\<close> between_inner_transitivity by blast
          obtain X0 where "Bet X X0 A" and "Cong A B X X0"
            using Le_def \<open>A B Le X A\<close> by blast
          {
            assume "\<not> Reach A B A X0"
            have "X Out X0 B" 
              by (metis \<open>A \<noteq> B\<close> \<open>Bet A B X\<close> \<open>Bet X X0 A\<close> \<open>Cong A B X X0\<close> \<open>X \<noteq> B\<close> 
                  bet_out bet_out_1 cong_reverse_identity l6_6 l6_7 not_cong_3421)
            hence False
              by (metis \<open>A \<noteq> B\<close> \<open>Bet A B X\<close> \<open>Bet X X0 A\<close> \<open>Cong A B X X0\<close> \<open>X Out X0 B\<close> 
                  \<open>\<forall>P Q. (P = A \<or> A Out B P \<and> Reach A B A P) \<and> A Out B Q \<and> \<not> Reach A B A Q 
                         \<longrightarrow> Bet P X Q\<close> 
                  \<open>\<not> Reach A B A X0\<close> bet2__out bet_cong_eq between_symmetry between_trivial2 
                  not_bet_and_out not_cong_1243)
          }
          hence "Reach A B A X0" 
            by blast
          moreover 
          {
            assume "Reach A B A X0"
            obtain B' where "Grad A B B'" and "A X0 Le A B'" 
              using Reach_def calculation by blast
            obtain B1' where "Bet A B' B1'" and "Cong B' B1' A B" 
              using segment_construction by blast
            have "Grad A B B1'" 
              using Cong_cases \<open>Bet A B' B1'\<close> \<open>Cong B' B1' A B\<close> \<open>Grad A B B'\<close> 
                grad_stab by blast
            moreover have "X0 X Le B' B1'" 
              by (meson \<open>Cong A B X X0\<close> \<open>Cong B' B1' A B\<close> cong_pseudo_reflexivity 
                  cong_transitivity l5_6 le_reflexivity)
            hence "A X Le A B1'" 
              using \<open>A X0 Le A B'\<close> \<open>Bet A B' B1'\<close> \<open>Bet X X0 A\<close> bet2_le2__le1346 
                between_symmetry by blast
            ultimately have "Reach A B A X" 
              using Reach_def by blast
            hence False 
              by (simp add: \<open>\<not> Reach A B A X\<close>)
          }
          ultimately have False 
            by blast
        }
        ultimately have False
          using local.le_cases by blast
      }
      ultimately have False 
        by blast
    } 
    hence "Reach A B A C" 
      by blast
  }
  thus ?thesis
    using archimedes_aux by blast
qed

lemma dedekind__archimedes:
  assumes "DedekindsAxiom" 
  shows "archimedes_axiom" 
  using assms dedekind_equiv dedekind_variant__archimedes by blast

subsubsection "Cantor variant"

definition NestedBis ::  "(nat \<Rightarrow> TPoint \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> TPoint \<Rightarrow> bool)=>bool"
  where
    "NestedBis A B \<equiv> 
(\<forall> n. \<exists> An Bn. A n An \<and> B n Bn) \<and>
(\<forall> n An An'. A n An \<and> A n An' \<longrightarrow> An = An') \<and>
(\<forall> n Bn Bn'. B n Bn \<and> B n Bn' \<longrightarrow> Bn = Bn') \<and>
(\<forall> n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn \<longrightarrow>
Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)"

definition CantorVariant :: bool
  where
    "CantorVariant \<equiv> \<forall> A B. NestedBis A B \<longrightarrow>
 (\<exists> X. \<forall> n An Bn. A n An \<and> B n Bn \<longrightarrow> Bet An X Bn)"

lemma nested_bis__nested:
  assumes "NestedBis A B" 
  shows "Nested A B" 
  using NestedBis_def Nested_def assms by presburger

lemma cantor__cantor_variant_1:
  assumes "CantorsAxiom" 
  shows "CantorVariant" 
  using CantorVariant_def CantorsAxiom_def assms nested_bis__nested by blast

lemma cantor__cantor_variant_2:
  assumes "CantorVariant"
  shows "CantorsAxiom" 
proof -
  (* have "\<forall> A B. NestedBis A B \<longrightarrow> (\<exists> X. \<forall> n An Bn. A n An \<and> B n Bn \<longrightarrow> Bet An X Bn)"
    using CantorVariant_def assms by blast
  hence "\<forall> A B. (\<forall> n. \<exists> An Bn. A n An \<and> B n Bn) \<and> 
                (\<forall> n An An'. A n An \<and> A n An' \<longrightarrow> An = An') \<and>
                (\<forall> n Bn Bn'. B n Bn \<and> B n Bn' \<longrightarrow> Bn = Bn') \<and>
                (\<forall> n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn \<longrightarrow>
                Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)
                \<longrightarrow> (\<exists> X. \<forall> n An Bn. A n An \<and> B n Bn \<longrightarrow> Bet An X Bn)"
    using NestedBis_def by auto
*)
  { 
    fix A B
    assume "Nested A B" 
    then obtain fA::"nat\<Rightarrow>TPoint" where "\<forall> x. A x (fA x)"
      by (metis nested__ex_right nested_sym) 
    obtain fB::"nat\<Rightarrow>TPoint" where "\<forall> x. B x (fB x)"
      using \<open>Nested A B\<close> nested__ex_right nested_sym by metis
    let ?f1 = "\<lambda> n::nat. \<lambda> An::TPoint. An = fA n"
    let ?f2 = "\<lambda> n::nat. \<lambda> Bn::TPoint. Bn = fB n"
    have "(\<forall> n. (\<exists> An Bn. A n An \<and> B n Bn)) \<and> (\<forall> n An Am Bm Bn.
                    (A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn) 
                    \<longrightarrow> (Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm))"
      using \<open>Nested A B\<close> Nested_def by auto
    have "NestedBis ?f1 ?f2" 
    proof -
      have "(\<forall> n. \<exists> An Bn. ?f1 n An \<and> ?f2 n Bn)" 
        by simp
      moreover have "(\<forall> n An An'. ?f1 n An \<and> ?f1 n An' \<longrightarrow> An = An')" 
        by simp
      moreover have "(\<forall> n Bn Bn'. ?f2 n Bn \<and> ?f2 n Bn' \<longrightarrow> Bn = Bn')" 
        by simp
      moreover have "(\<forall> n An Am Bm Bn. ?f1 n An \<and> ?f1 (Suc n) Am \<and>  
                           ?f2 (Suc n) Bm \<and> ?f2 n Bn \<longrightarrow> 
                      Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)"
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
                    (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                     \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> 
          \<open>\<forall>x. A x (fA x)\<close> \<open>\<forall>x. B x (fB x)\<close> by blast
      ultimately show ?thesis 
        using NestedBis_def by presburger
    qed
    hence "\<exists> X. \<forall> n An Bn. An = fA n \<and> Bn = fB n  \<longrightarrow> Bet An X Bn"
      using assms(1) CantorVariant_def by blast
    then obtain X where "\<forall> n An Bn. An = fA n \<and> Bn = fB n  \<longrightarrow> Bet An X Bn"
      by blast
    {
      fix n An Bn
      assume "A n An" and "B n Bn"
      have "Bet An (fA (Suc n)) (fB (Suc n))" 
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
                (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                 \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> 
          \<open>A n An\<close> \<open>\<forall>x. A x (fA x)\<close> \<open>\<forall>x. B x (fB x)\<close> by blast
      moreover have "Bet (fA (Suc n)) (fB (Suc n)) Bn" 
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
               (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
               \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> \<open>B n Bn\<close> 
          \<open>\<forall>x. A x (fA x)\<close> \<open>\<forall>x. B x (fB x)\<close> by blast
      moreover have "fA (Suc n) \<noteq> fB (Suc n)" 
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
                (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                  \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> 
          \<open>\<forall>x. A x (fA x)\<close> \<open>\<forall>x. B x (fB x)\<close> by blast
      moreover have "Bet (fA (Suc n)) X (fB (Suc n))" 
        by (simp add: \<open>\<forall>n An Bn. An = fA n \<and> Bn = fB n \<longrightarrow> Bet An X Bn\<close>)
      ultimately have "Bet An X Bn" 
        by (meson bet3__bet between_exchange4 outer_transitivity_between2)
    }
    hence "\<exists> X. \<forall> n An Bn. (A n An \<and> B n Bn) \<longrightarrow> Bet An X Bn" 
      by blast
  }
  thus ?thesis 
    using CantorsAxiom_def by blast
qed

lemma cantor__cantor_variant:
  shows "CantorsAxiom \<longleftrightarrow> CantorVariant" 
  using cantor__cantor_variant_1 cantor__cantor_variant_2 by blast
    (*
subsubsection "Completeness"

definition inj:: "(TPoint \<Rightarrow> TPoint) \<Rightarrow> bool"
  where
  "inj f \<equiv> \<forall> A B::TPoint. f A = f B \<longrightarrow> A = B" 

definition pres_bet:: "(TPoint\<Rightarrow>TPoint) \<Rightarrow>bool"
  where 
"pres_bet f \<equiv> \<forall> A B C. Bet A B C \<longrightarrow> Bet (f A) (f B) (f C)"

definition pres_cong :: "(TPoint\<Rightarrow>TPoint) \<Rightarrow>bool"
  where
"pres_cong f \<equiv> \<forall> A B C D. Cong A B C D \<longrightarrow> Cong (f A) (f B) (f C) (f D)"

definition extension:: "(TPoint\<Rightarrow>TPoint) \<Rightarrow> bool"
  where
"extension f \<equiv> inj f \<and> pres_bet f \<and> pres_cong f"
(*
Definition completeness_for_planes := forall (Tm: Tarski_neutral_dimensionless)
  (Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm)
  (M : Tarski_2D Tm2)
  (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  extension f ->
  forall A, exists B, f B = A.

Definition completeness_for_3d_spaces := forall (Tm: Tarski_neutral_dimensionless)
  (Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm)
  (M : Tarski_3D Tm2)
  (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  extension f ->
  forall A, exists B, f B = A.
*)
definition inj_line :: "(TPoint\<Rightarrow>TPoint)\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool"
  where
"inj_line f P Q \<equiv> \<forall> A B. Col P Q A \<and> Col P Q B \<and> f A = f B \<longrightarrow> A = B"

definition pres_bet_line :: "(TPoint\<Rightarrow>TPoint)\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool"
  where
"pres_bet_line f P Q \<equiv> \<forall> A B C. Col P Q A \<and> Col P Q B \<and> Col P Q C \<and> Bet A B C \<longrightarrow> Bet (f A)(f B)(f C)"

definition pres_cong_line :: "(TPoint\<Rightarrow>TPoint)\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool"
  where
"pres_cong_line f P Q \<equiv> \<forall> A B C D. Col P Q A \<and> Col P Q B \<and> Col P Q C \<and> Col P Q D \<and> 
Cong A B C D \<longrightarrow> Cong (f A) (f B) (f C) (f D)"

definition line_extension :: "(TPoint\<Rightarrow>TPoint)\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool"
  where
"line_extension f P Q \<equiv> P \<noteq> Q \<and> inj_line f P Q \<and> pres_bet_line f P Q \<and> pres_cong_line f P Q"

(** Rmq: ici Tm = Tm2 **)
definition line_completeness :: bool
  where
"line_completeness \<equiv> archimedes_axiom \<and> 
(\<forall> f. \<forall> P Q. line_extension f P Q 
\<longrightarrow>
(\<forall> A. Col (f P) (f Q) A \<longrightarrow> (\<exists> B. Col P Q B \<and> f B = A)))"

lemma inj_line_symmetry:
  assumes "inj_line f P Q"
  shows "inj_line f Q P" 
  by (metis NCol_cases assms inj_line_def)

lemma pres_bet_line_symmetry:
  assumes "pres_bet_line f P Q"
  shows "pres_bet_line f Q P"
  by (metis assms not_col_permutation_4 pres_bet_line_def)

lemma pres_cong_line_symmetry:
  assumes "pres_cong_line f P Q"
  shows "pres_cong_line f Q P" 
proof -
  { 
    fix A B C D
    assume "Col Q P A" and "Col Q P B" and "Col Q P C" and
"Col Q P D" and "Cong A B C D"
    have "Col P Q A" 
      using NCol_cases \<open>Col Q P A\<close> by blast
      moreover have "Col P Q B" 
        using \<open>Col Q P B\<close> col_permutation_4 by blast
        moreover have "Col P Q C" 
          using NCol_cases \<open>Col Q P C\<close> by blast
          moreover have "Col P Q D" 
            using Col_cases \<open>Col Q P D\<close> by auto
            ultimately have "Cong (f A) (f B) (f C) (f D)" 
              using \<open>Cong A B C D\<close> assms pres_cong_line_def by blast
    }
    thus ?thesis 
      using assms not_col_permutation_4 pres_cong_line_def by blast
qed

lemma line_extension_symmetry:
  assumes "line_extension f P Q"
  shows "line_extension f Q P"
proof -
  have "Q \<noteq> P" 
    using assms line_extension_def by auto
  moreover have "inj_line f Q P" 
    using assms inj_line_symmetry line_extension_def by blast
  moreover have "pres_bet_line f Q P" 
    by (meson assms line_extension_def pres_bet_line_symmetry)
  moreover have "pres_cong_line f Q P" 
    by (meson assms line_extension_def pres_cong_line_symmetry)
  ultimately show ?thesis
  using line_extension_def by blast
qed

lemma inj_line_stability:
  assumes "Col P Q R" and
"P \<noteq> R" and
"inj_line f P Q"
shows "inj_line f P R" 
proof -
  {
    fix A B
    assume "Col P R A" and "Col P R B" and "f A = f B"
    moreover have "Col P Q A" 
      by (meson assms(1) assms(2) calculation(1) colx not_col_distincts)
    moreover have "Col P Q B" 
      using assms(1) assms(2) calculation(2) col_trivial_3 colx by blast
    ultimately have "A = B" 
      using assms(3) inj_line_def by blast
    }
    thus ?thesis 
      using inj_line_def by force
qed

lemma pres_bet_line_stability:
  assumes "Col P Q R" and
"P \<noteq> R" and
"pres_bet_line f P Q"
shows "pres_bet_line f P R" 
proof -
  {
  fix A B C
  assume "Col P R A" and "Col P R B" and "Col P R C" and "Bet A B C"
  have "Col P Q A" 
    using \<open>Col P R A\<close> assms(1) assms(2) col_trivial_3 colx by blast
    moreover have "Col P Q B" 
      using \<open>Col P R B\<close> assms(1) assms(2) col_trivial_3 colx by blast
      moreover have "Col P Q C" 
        using \<open>Col P R C\<close> assms(1) assms(2) col_trivial_3 colx by blast
        ultimately have "Bet (f A)(f B)(f C)" 
          using \<open>Bet A B C\<close> assms(3) pres_bet_line_def by blast
}
  thus ?thesis 
    using pres_bet_line_def by force
  qed

lemma pres_cong_line_stability:
  assumes "Col P Q R" and
"P \<noteq> R" and
"pres_cong_line f P Q"
shows "pres_cong_line f P R" 
proof -
  {
    fix A B C D
    assume "Col P R A" and "Col P R B" and "Col P R C" and "Col P R D" and "Cong A B C D"
    have "Col P Q A" 
      using \<open>Col P R A\<close> assms(1) assms(2) col_trivial_3 colx by blast
      moreover have "Col P Q B" 
        using \<open>Col P R B\<close> assms(1) assms(2) col_trivial_3 colx by blast
      moreover have "Col P Q C" 
        by (meson \<open>Col P R C\<close> assms(1) assms(2) colx not_col_distincts)
      moreover have "Col P Q D" 
        by (meson \<open>Col P R D\<close> assms(1) assms(2) colx not_col_distincts)
        ultimately have "Cong (f A) (f B) (f C) (f D)" 
          using \<open>Cong A B C D\<close> assms(3) pres_cong_line_def by blast
  }
  thus ?thesis 
    using pres_cong_line_def by force
qed

lemma line_extension_stability:
  assumes "Col P Q R" and
"P \<noteq> R" and
"line_extension f P Q"
shows "line_extension f P R" 
  using assms(1) assms(2) assms(3) inj_line_stability line_extension_def pres_bet_line_stability pres_cong_line_stability by auto

lemma line_extension_reverse_bet:
  assumes "line_extension f P Q" and
"Col P Q A" and
"Col P Q B" and
"Col P Q C" and
"Bet (f A) (f B) (f C)"
shows "Bet A B C" 
proof -
  have "pres_bet_line f P Q" 
    using assms(1) line_extension_def by auto
  have "inj_line f P Q" 
    using assms(1) line_extension_def by auto
  have "Col A B C" 
    using assms(1) assms(2) assms(3) assms(4) col3 line_extension_def by blast
  hence "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    by (simp add: Col_def)
  moreover {
    assume "Bet B C A"
    hence "f B = f C" 
      by (meson assms(1) assms(2) assms(3) assms(4) assms(5) between_equality_2 between_symmetry line_extension_def pres_bet_line_def)
    hence "B = C" 
      using assms(3) assms(4) inj_line_def \<open>inj_line f P Q\<close> by blast
    hence "Bet A B C" 
      by (simp add: between_trivial)
    }
    moreover {
      assume  "Bet C A B" 
      hence "f A = f B" 
        using \<open>pres_bet_line f P Q\<close> assms(2) assms(3) assms(4) assms(5) between_equality between_symmetry pres_bet_line_def by blast
    hence "A = B" 
      using \<open>inj_line f P Q\<close> assms(2) assms(3) inj_line_def by blast
    hence "Bet A B C" 
      by (simp add: between_trivial2)
    }
      ultimately show ?thesis 
        by blast
qed

lemma pres_bet_line__col:
  assumes "P \<noteq> Q" and 
"pres_bet_line f P Q" and
"Col P Q A" and
"Col P Q B" and
"Col P Q C" 
shows "Col (f A) (f B) (f C)"
proof -
  have "Col A B C"
    using col3 [where ?X="P" and ?Y="Q"] assms(1) assms(3) assms(4) assms(5) by blast
  thus ?thesis 
    by (meson Col_def assms(2) assms(3) assms(4) assms(5) pres_bet_line_def)
qed

lemma col2_diff_inj_line__diff:
assumes "inj_line f P Q" and
"Col P Q A" and
"Col P Q B" and
"A \<noteq> B"
shows "f A \<noteq> f B" 
  using assms(1) assms(2) assms(3) assms(4) inj_line_def by blast

lemma extension__line_extension:
  assumes "P \<noteq> Q" and
"extension f"
shows "line_extension f P Q"
proof -
  have "inj f"
    using assms(2) extension_def by auto
  have "pres_bet f" 
    using assms(2) extension_def by auto
  have "pres_cong f"
    using assms(2) extension_def by auto
  moreover have "inj_line f P Q" 
    using \<open>local.inj f\<close> inj_line_def local.inj_def by blast
  moreover have "pres_bet_line f P Q"   
    using \<open>pres_bet f\<close> pres_bet_def pres_bet_line_def by auto
  moreover have "pres_cong_line f P Q"
    using \<open>pres_cong f\<close> pres_cong_def pres_cong_line_def by auto
  ultimately show ?thesis
  using line_extension_def assms(1) by blast
qed

lemma extension_reverse_bet:
  assumes "extension f" and
"Bet (f A) (f B) (f C)" 
shows "Bet A B C" 
proof (cases "(f A) = (f B)")
  case True
  have "inj f"
    using assms(1) extension_def by auto
  hence "A = B" 
    using True local.inj_def by blast
  then show ?thesis 
    by (simp add: between_trivial2)
next
  case False
  hence "(f A) \<noteq> (f B)" 
    by blast
  have "inj f"
    using assms(1) extension_def by auto
  obtain D where "Bet A B D" and "Cong B D B C" 
    using segment_construction by fastforce
  have "(f C) = (f D)"
  proof (rule between_cong_3 [where ?A="(f A)" and ?B="(f B)"])
 show "f A \<noteq> f B" 
   by (simp add: False)
 show "Bet (f A) (f B) (f C)"
   by (simp add: assms(2))
 show "Bet (f A) (f B) (f D)"
   using \<open>Bet A B D\<close> assms(1) extension_def pres_bet_def by blast
 show "Cong (f B) (f C) (f B) (f D)"
   using \<open>Cong B D B C\<close> assms(1) extension_def not_cong_3412 pres_cong_def by blast
  qed
  hence "C = D"
    using \<open>local.inj f\<close> local.inj_def by blast
  then show ?thesis 
    by (simp add: \<open>Bet A B D\<close>)
qed

lemma extension_reverse_col:
  assumes "extension f" and
"Col (f A) (f B) (f C)"
shows "Col A B C" 
proof -
  have "Bet (f A) (f B) (f C) \<longrightarrow> Bet A B C" 
    using assms(1) extension_reverse_bet by blast
  moreover have "Bet (f B) (f C) (f A) \<longrightarrow> Bet B C A" 
    using assms(1) extension_reverse_bet by blast
  moreover have "Bet (f C) (f A) (f B) \<longrightarrow> Bet C A B" 
    using assms(1) extension_reverse_bet by blast
  ultimately show ?thesis 
    using Col_def assms(1) assms(2) extension_reverse_bet by blast
  qed

(** The following section is inspired by Theorem 32 of Hilbert's Foundations of Geometry (10th edition).
    It deduces completeness of a 2 or 3-dimensional space from completeness of lines.
    The original proof is due to Paul Bernays. *)

lemma line_completeness_aux: 
  assumes "line_completeness" and
    "archimedes_axiom" and
    "extension f" and
    "\<not> Col P Q R" and
    "Coplanar (f P) (f Q) (f R) A"
  shows "\<exists> B. Coplanar P Q R B \<and> f B = A"
proof -
  have "archimedes_axiom"
    using assms(1) line_completeness_def by blast
  have "\<forall> f. \<forall> P Q. line_extension f P Q \<longrightarrow>
(\<forall> A. Col (f P) (f Q) A \<longrightarrow> (\<exists> B. Col P Q B \<and> f B = A))" 
    using assms(1) line_completeness_def by blast
  {
    fix X Y ::TPoint
    assume "X \<noteq> Y"
    hence "line_extension f X Y" 
      by (simp add: assms(3) extension__line_extension)
  }
  obtain S where "S Midpoint P Q" 
    using MidR_uniq_aux by blast
  show "\<exists> B. Coplanar P Q R B \<and> f B = A"
  proof (cases "Col (f R) (f S) A")
    case True
    {
      assume "R = S"
      hence "Col P Q R" 
        using \<open>S Midpoint P Q\<close> col_permutation_1 midpoint_col by blast
      hence False 
        by (simp add: assms(4))
    }
    hence "R \<noteq> S" 
      by blast
    hence "\<exists> B. Col R S B \<and> (f B) = A" 
      using assms(1) line_completeness_def True \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> by presburger
    then obtain B where "Col R S B" and "(f B) = A"
      by blast
    moreover
    hence "Coplanar P Q R B" 
      using Coplanar_def Midpoint_def \<open>S Midpoint P Q\<close> bet_col1 between_exchange2 between_symmetry not_col_permutation_5 point_construction_different by meson
    ultimately show ?thesis
      by blast
  next
    case False
    hence "\<not> Col (f R) (f S) A"
      by simp
    show ?thesis 
    proof (cases "Col (f P) (f Q) A")
      case True
      have "\<exists> B. Col P Q B \<and> (f B) = A" 
        using assms(1) line_completeness_def by (metis True \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> assms(4) col_permutation_2 col_trivial_3)
      then obtain B0 where "Col P Q B0" and "f B0 = A" 
        by blast
      hence "Coplanar P Q R B0" 
        using ncop__ncols by blast
      thus ?thesis 
        using \<open>f B0 = A\<close> by blast
    next
      case False
      hence "\<not> Col (f P) (f Q) A"
        by simp
      hence "\<exists> X. Col A (f S) X \<and> (BetS (f P) X (f R) \<or> BetS (f Q) X (f R))" 
      proof -
        have "Coplanar (f P) (f Q) (f R) A" 
          by (simp add: assms(5))
        moreover have "\<not> Col (f R) (f S) A" 
          by (simp add: \<open>\<not> Col (f R) (f S) A\<close>)
        moreover have "\<not> Col (f P) (f Q) A" 
          by (simp add: False)
        moreover have "BetS (f P) (f S)(f Q)" 
          by (metis BetS_def False Midpoint_def \<open>S Midpoint P Q\<close> assms(3) col_trivial_3 extension_def local.inj_def midpoint_distinct_1 not_col_permutation_5 pres_bet_def)
        ultimately show ?thesis
          by (simp add: hilbert_s_version_of_pasch)
      qed
      then obtain X where "Col A (f S) X" and "BetS (f P) X (f R) \<or> BetS (f Q) X (f R)"
        by blast
      have "\<exists> Y. Coplanar P Q R Y \<and> (f Y) = X" 
      proof -
        {
          assume "BetS (f P) X (f R)"
          hence "\<exists> Y. Col P R Y \<and> (f Y) = X"
            using assms(1) line_completeness_def by (metis BetSEq Col_def \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> between_symmetry)
          hence "\<exists> Y. Coplanar P Q R Y \<and> (f Y) = X"
            using ncop__ncols by blast
        }
        moreover {
          assume "BetS (f Q) X (f R)"
          hence "\<exists> Y. Col Q R Y \<and> (f Y) = X" 
            using assms(1) line_completeness_def by (metis BetSEq Col_def \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> between_symmetry)
          hence "\<exists> Y. Coplanar P Q R Y \<and> (f Y) = X" 
            using ncop__ncols by blast
        }
        ultimately show ?thesis 
          using \<open>BetS (f P) X (f R) \<or> BetS (f Q) X (f R)\<close> by blast
      qed
      then obtain Y where "Coplanar P Q R Y" and "(f Y) = X" 
        by blast
      {
        assume "S = Y"
        have "Bet P S Q" 
          using Midpoint_def \<open>S Midpoint P Q\<close> by auto
        hence "Bet (f P) (f S) (f Q)" 
          using assms(3) extension_def pres_bet_def by blast
        have "BetS (f P) (f S) (f R) \<or> BetS (f Q) (f S) (f R)" 
          by (simp add: \<open>BetS (f P) X (f R) \<or> BetS (f Q) X (f R)\<close> \<open>S = Y\<close> \<open>f Y = X\<close>)
        moreover
        have "BetS (f P) (f S) (f R) \<longrightarrow> Col (f P) (f Q) (f R)" 
          using BetSEq Col_def \<open>Bet (f P) (f S) (f Q)\<close> between_symmetry l5_1 by blast
        moreover {
          assume "BetS (f Q) (f S) (f R)" 
          have "f S \<noteq> f Q" 
            by (metis BetSEq \<open>BetS (f Q) (f S) (f R)\<close>)
          moreover have "Col (f S) (f Q) (f P)" 
            by (simp add: Col_def \<open>Bet (f P) (f S) (f Q)\<close>)
          moreover have "Col (f S) (f Q) (f R)" 
            using BetSEq Bet_cases Col_def \<open>BetS (f Q) (f S) (f R)\<close> by blast
          ultimately have "Col (f P) (f Q) (f R)" 
            using col3 col_trivial_2 by blast
        }
        ultimately have "Col (f P) (f Q) (f R)" 
          by blast
        hence "Col P Q R"
          using assms(3) extension_reverse_col by blast
        hence False 
          by (simp add: assms(4))
      }
      hence "S \<noteq> Y" 
        by blast
      obtain B where "Col S Y B" and "(f B) = A" 
        using assms(1) line_completeness_def Col_cases \<open>Col A (f S) X\<close> \<open>S = Y \<Longrightarrow> False\<close> \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> \<open>f Y = X\<close> by blast
      have "Coplanar P Q R S" 
        using Col_def Midpoint_def \<open>S Midpoint P Q\<close> between_symmetry ncop__ncols by blast
      hence "Coplanar P Q R B" 
        using col_cop2__cop [where ?U = "S" and ?V = "Y"] \<open>Col S Y B\<close> \<open>Coplanar P Q R Y\<close> \<open>S \<noteq> Y\<close> by blast
      thus ?thesis 
        using \<open>f B = A\<close> by blast
    qed
  qed
qed

(*lemma line_completeness__completeness_for_planes:
  assumes "line_completeness" 
  shows "completeness_for_planes" sorry
*)
*)

subsubsection "Elementary continuity props"
  (**    All these properties are known to be equivalent in an arbitrary Hilbert plane (Tarski_2D)
  as shown by Strommer, but we don't have formalized the proof yet.

  We have the following proofs:
  - five equivalent variants of the circle-circle continuity axiom;
  - three equivalent variants of the line-circle continuity axiom;
  - the implication from the circle-circle continuity axiom to the line-circle continuity axiom.

  Since we have proved the circle-circle continuity axiom to follow from Tarski's axiom of continuity,
  all these properties do.
*)

lemma segment_circle__one_point_line_circle_R1:
  assumes "SegmentCircle" 
  shows "OnePointLineCircle" 
proof -
  {
    fix A B U V P
    assume "Col U V P" and "U \<noteq> V" and "Bet A P B" 
    have "\<exists> Z. Col U V Z \<and> Z OnCircle A B" 
    proof (cases "A = B")
      case True
      thus ?thesis 
        using \<open>Bet A P B\<close> \<open>Col U V P\<close> between_identity onc212 by blast
    next
      case False
      hence "A \<noteq> B" 
        by simp
      have "P InCircle A B" 
        by (simp add: InCircle_def \<open>Bet A P B\<close> bet__le1213)
      obtain W where "U \<noteq> W" and "V \<noteq> W" and "P \<noteq> W" and "Col U V W" 
        using \<open>Col U V P\<close> diff_col_ex3 by blast
      show ?thesis 
      proof (cases "A = P")
        case True
        obtain Q where "Bet W A Q" and "Cong A Q A B" 
          using segment_construction by blast
        hence "Q OutCircle A B" 
          using OnCircle_def onc__outc by blast
        then obtain Z where "Bet A Z Q" and "Z OnCircle A B" 
          using segment_circle_def True \<open>P InCircle A B\<close> assms by blast
        have "Col U V Z"
          by (metis Col_def OnCircle_def True \<open>Bet A Z Q\<close> \<open>Bet W A Q\<close> 
              \<open>Col U V P\<close> \<open>Col U V W\<close> \<open>Cong A Q A B\<close> \<open>P \<noteq> W\<close> \<open>Z OnCircle A B\<close> 
              bet_cong_eq between_symmetry between_trivial col_transitivity_1) 
        thus ?thesis 
          using \<open>Z OnCircle A B\<close> by blast
      next
        case False
        hence "A \<noteq> P" 
          by simp
        obtain Q0 where "Bet W P Q0" and "Cong P Q0 P A" 
          using segment_construction by blast
        obtain Q where "Bet P Q0 Q" and "Cong Q0 Q A B" 
          using segment_construction by blast
        have "P Out Q Q0" 
          by (metis False \<open>Bet P Q0 Q\<close> \<open>Cong P Q0 P A\<close> bet_out cong_reverse_identity l6_6)
        hence "Q Q0 Le Q A" 
          using \<open>Cong P Q0 P A\<close> not_cong_3412 triangle_reverse_inequality by blast
        hence "Q OutCircle A B" 
          using l5_6 by (meson OutCircle_def \<open>Cong Q0 Q A B\<close> 
              cong_pseudo_reflexivity not_cong_4312)
        then obtain Z where "Bet P Z Q" and "Z OnCircle A B" 
          using segment_circle_def \<open>P InCircle A B\<close> assms by blast
        hence "Col U V Z" 
          by (metis Col_def Out_def \<open>Bet W P Q0\<close> \<open>Col U V P\<close> 
              \<open>Col U V W\<close> \<open>P Out Q Q0\<close> \<open>P \<noteq> W\<close> colx)
        then show ?thesis 
          using \<open>Z OnCircle A B\<close> by blast
      qed 
    qed
  }
  thus ?thesis 
    using one_point_line_circle_def by blast
qed

lemma segment_circle__one_point_line_circle_R2:
  assumes "OnePointLineCircle" 
  shows "SegmentCircle" 
proof -
  {
    fix A B P Q
    assume "P InCircle A B" and
      "Q OutCircle A B" 
    have "\<exists> Z. Bet P Z Q \<and> Z OnCircle A B" 
    proof (cases "A = B")
      case True
      thus ?thesis 
        using \<open>P InCircle A B\<close> between_trivial2 inc_eq onc212 by blast
    next
      case False
      hence "A \<noteq> B" 
        by simp
      show ?thesis
      proof (cases "P = Q")
        case True
        then show ?thesis 
          using \<open>P InCircle A B\<close> \<open>Q OutCircle A B\<close> inc_outc__onc not_bet_distincts by blast
      next
        case False
        hence "P \<noteq> Q"
          by simp
        show ?thesis 
        proof (cases "Cong A B A Q")
          case True
          then show ?thesis 
            by (meson OnCircle_def not_bet_distincts onc_sym)
        next
          case False
          hence "\<not> Cong A B A Q"
            by simp
          then obtain B' where "Cong A B A B'" and "Bet A P B'"
            using OnCircle_def \<open>P InCircle A B\<close> inc__radius onc_sym by blast
          obtain Z1 where "Col P Q Z1" and "Z1 OnCircle A B'" 
            using assms one_point_line_circle_def 
            by (meson \<open>Bet A P B'\<close> \<open>P \<noteq> Q\<close> not_col_distincts)
          have "Z1 OnCircle A B" 
            using EqC_def \<open>Cong A B A B'\<close> \<open>Z1 OnCircle A B'\<close> eqc_chara_2 by presburger
          have "Bet P Z1 Q \<longrightarrow> ?thesis" 
            using \<open>Z1 OnCircle A B\<close> by auto
          moreover 
          {
            assume "Z1 Out P Q" 
            obtain Z2 where "Z2 OnCircle A B" and "Bet Z1 P Z2" 
              using \<open>P InCircle A B\<close> \<open>Z1 OnCircle A B\<close> chord_completion by blast
            have "Bet Z1 Z2 Q" 
            proof -
              have "Z1 Out Z2 Q" 
                by (metis Out_def \<open>Bet Z1 P Z2\<close> \<open>Z1 Out P Q\<close> bet_neq12__neq l6_7)
              moreover have "Q Out Z1 Z2" 
              proof (rule col_inc2_outcs__out [where ?A="A" and ?B="B"])
                show "Z1 InCircle A B" 
                  by (simp add: \<open>Z1 OnCircle A B\<close> onc__inc) 
                show "Z2 InCircle A B" 
                  using \<open>Z2 OnCircle A B\<close> onc__inc by auto 
                show "Col Z1 Z2 Q" 
                  by (simp add: calculation out_col)
                show "Q OutCircleS A B" 
                  using False OnCircle_def \<open>Q OutCircle A B\<close> circle_cases 
                    not_cong_3412 outc__nincs_1 by blast
              qed
              ultimately show ?thesis 
                using out2__bet by blast
            qed
            hence "Bet P Z2 Q" 
              using \<open>Bet Z1 P Z2\<close> between_exchange3 by blast
            hence ?thesis 
              using \<open>Z2 OnCircle A B\<close> by blast
          }
          moreover have "\<not> Col P Z1 Q \<longrightarrow> ?thesis" 
            using Col_perm \<open>Col P Q Z1\<close> by blast
          ultimately
          show ?thesis 
            using l6_4_2 by blast
        qed
      qed
    qed
  }
  thus ?thesis 
    by (simp add: segment_circle_def)
qed

lemma segment_circle__one_point_line_circle:
  shows "SegmentCircle \<longleftrightarrow> OnePointLineCircle" 
  using segment_circle__one_point_line_circle_R1 
    segment_circle__one_point_line_circle_R2 by blast

lemma one_point_line_circle__two_points_line_circle_R1 :
  assumes "one_point_line_circle" 
  shows "two_points_line_circle"
proof -
  {
    fix A B U V P
    assume "Col U V P" and "U \<noteq> V" and "Bet A P B"
    have "\<exists> Z1 Z2. Col U V Z1 \<and> Z1 OnCircle A B \<and>
                Col U V Z2 \<and> Z2 OnCircle A B \<and>
                Bet Z1 P Z2 \<and> (P \<noteq> B \<longrightarrow> Z1 \<noteq> Z2)" 
    proof (cases "P = B")
      case True
      then show ?thesis 
        using \<open>Col U V P\<close> between_trivial2 onc212 by blast
    next
      case False
      hence "P \<noteq> B" 
        by simp
      obtain Z1 where "Col U V Z1" and "Z1 OnCircle A B" 
        using \<open>Bet A P B\<close> \<open>Col U V P\<close> \<open>U \<noteq> V\<close> assms one_point_line_circle_def by blast
      have "P InCircle A B" 
        using \<open>Bet A P B\<close> bet_inc2__inc inc112 onc212 onc__inc by blast
      then obtain Z2 where "Z2 OnCircle A B" and "Bet Z1 P Z2" 
        using chord_completion \<open>Z1 OnCircle A B\<close> by blast
      have "Z1 \<noteq> P" 
        using False \<open>Bet A P B\<close> \<open>Z1 OnCircle A B\<close> between_cong onc212 onc2__cong by blast
      thus ?thesis 
        by (metis \<open>Col U V P\<close> \<open>Col U V Z1\<close> \<open>Z1 OnCircle A B\<close> 
            \<open>\<And>thesis. (\<And>Z2. \<lbrakk>Z2 OnCircle A B ; Bet Z1 P Z2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
            bet_col between_equality colx outer_transitivity_between point_construction_different)
    qed
  }
  thus ?thesis 
    using two_points_line_circle_def by blast
qed

lemma one_point_line_circle__two_points_line_circle_R2 :
  assumes "two_points_line_circle"
  shows "one_point_line_circle" 
  using assms two_points_line_circle_def one_point_line_circle_def by blast

lemma one_point_line_circle__two_points_line_circle :
  shows "one_point_line_circle \<longleftrightarrow> two_points_line_circle" 
  using one_point_line_circle__two_points_line_circle_R1 
    one_point_line_circle__two_points_line_circle_R2 by blast

lemma circle_circle_bis__circle_circle_axiom_R1: 
  assumes "circle_circle_bis" 
  shows "circle_circle_axiom" 
proof -
  {
    fix A B C D B' D'
    assume "Cong A B' A B" and "Cong C D' C D" and
      "Bet A D' B" and "Bet C B' D"
    have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D"
    proof -
      have "D' OnCircle C D" 
        by (simp add: OnCircle_def \<open>Cong C D' C D\<close>)
      moreover have "D' InCircle A B" 
        using \<open>Bet A D' B\<close> bet_inc2__inc inc112 inc__outc incs__inc outc__nincs by blast
      moreover have "B' OnCircle A B" 
        by (simp add: OnCircle_def \<open>Cong A B' A B\<close>)
      moreover have "B' InCircle C D" 
        using \<open>Bet C B' D\<close> bet_inc2__inc inc112 onc212 onc__inc by blast
      ultimately show ?thesis
        using assms circle_circle_bis_def by blast
    qed
    hence "\<exists> Z. Cong A Z A B \<and> Cong C Z C D" 
      using OnCircle_def by blast
  }
  thus ?thesis 
    using circle_circle_axiom_def by blast
qed

lemma circle_circle_bis__circle_circle_axiom_R2:
  assumes "circle_circle_axiom" 
  shows "circle_circle_bis" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "P InCircle A B" and "Q OnCircle A B" and "Q InCircle C D"
    hence "A P Le A Q" 
      using InCircle_def OnCircle_def cong_reflexivity l5_6 onc_sym by blast
    then obtain Q' where "Bet A P Q'" and "Cong A Q' A Q" 
      using l5_5_1 by blast
    have "C Q Le C P" 
      using InCircle_def OnCircle_def \<open>P OnCircle C D\<close> \<open>Q InCircle C D\<close> 
        cong__le3412 le_transitivity by blast
    then obtain P' where "Bet C Q P'" and "Cong C P' C P" 
      using l5_5_1 by blast
    have "Cong A Q A Q'" 
      using \<open>Cong A Q' A Q\<close> not_cong_3412 by blast
    moreover have "Cong C P C P'" 
      by (simp add: \<open>Cong C P' C P\<close> cong_symmetry)
    ultimately obtain Z where "Cong A Z A Q'" and "Cong C Z C P'" 
      using \<open>Bet A P Q'\<close> \<open>Bet C Q P'\<close> assms circle_circle_axiom_def by blast
    have "Z OnCircle A B" 
      using OnCircle_def \<open>Cong A Q' A Q\<close> \<open>Cong A Z A Q'\<close> 
        \<open>Q OnCircle A B\<close> cong_transitivity by blast
    moreover have "Z OnCircle C D" 
      using OnCircle_def \<open>Cong C P' C P\<close> \<open>Cong C Z C P'\<close> 
        \<open>P OnCircle C D\<close> cong_transitivity by blast
    ultimately have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
      by blast
  }
  thus ?thesis 
    using circle_circle_bis_def by blast
qed

lemma circle_circle_bis__circle_circle_axiom:
  shows "circle_circle_bis \<longleftrightarrow> circle_circle_axiom" 
  using circle_circle_bis__circle_circle_axiom_R1 
    circle_circle_bis__circle_circle_axiom_R2 by blast

lemma circle_circle__circle_circle_bis:
  assumes "circle_circle"
  shows "circle_circle_bis" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "P InCircle A B" and "Q OnCircle A B" and "Q InCircle C D"
    have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
    proof (cases "P = Q")
      case True
      thus ?thesis 
        using \<open>P OnCircle C D\<close> \<open>Q OnCircle A B\<close> by blast
    next
      case False
      hence "P \<noteq> Q"
        by simp
      obtain P' where "P' OnCircle C D" and "Bet P Q P'" 
        using \<open>P OnCircle C D\<close> \<open>Q InCircle C D\<close> chord_completion by blast
      obtain Q' where "Q' OnCircle A B" and "Bet Q P Q'" 
        using \<open>P InCircle A B\<close> \<open>Q OnCircle A B\<close> chord_completion by blast
      have "P' OutCircle A B" 
        by (metis False \<open>Bet P Q P'\<close> \<open>P InCircle A B\<close> \<open>Q OnCircle A B\<close> 
            bet_inc2__incs incs__inc onc__outc outc__nincs) 
      thus ?thesis 
        using \<open>P InCircle A B\<close> \<open>P OnCircle C D\<close> \<open>P' OnCircle C D\<close> 
          assms circle_circle_def by blast
    qed
  }
  thus ?thesis 
    using circle_circle_bis_def by blast
qed

lemma circle_circle_bis__one_point_line_circle_aux:
  assumes "circle_circle_bis" and
    "Col U V P" and "U \<noteq> V" and "Bet A P B" and "\<not> Per A U V"
  shows "\<exists> Z. Col U V Z \<and> Z OnCircle A B" 
proof (cases "Col U V B")
  case True
  thus ?thesis 
    using onc212 by blast
next
  case False
  hence "\<not> Col U V B" 
    by simp
  show ?thesis 
  proof (cases "A = P")
    case True
    obtain W where "U \<noteq> W" and "V \<noteq> W" and "A \<noteq> W" and "Col U V W" 
      using assms(2) diff_col_ex3 by blast
    obtain Z where "Bet W A Z" and "Cong A Z A B" 
      using segment_construction by blast
    hence "Col U V Z" 
      by (metis True \<open>A \<noteq> W\<close> \<open>Col U V W\<close> assms(2) bet_col col3 not_col_distincts)
    moreover have "Z OnCircle A B" 
      by (simp add: OnCircle_def \<open>Cong A Z A B\<close>)
    ultimately show ?thesis 
      by blast
  next
    case False
    hence "A \<noteq> P" 
      by simp
    obtain C where "A C Reflect U V" 
      using l10_6_existence by blast
    obtain D where "B D Reflect U V" 
      using l10_6_existence by blast
    hence "Bet C P D" 
      using \<open>A C Reflect U V\<close> assms(4) assms(2) assms(3) image_gen_preserves_bet 
        l10_6_existence local.image_id by blast
    have "Cong B P D P" 
      using \<open>B D Reflect U V\<close> assms(3) assms(2) is_image_col_cong by blast
    have "Cong P D P B" 
      using Cong_cases \<open>Cong B P D P\<close> by blast
    hence "D InCircle A B" 
      using triangle_inequality InCircle_def assms(4) by blast 
    have "Cong P B P D" 
      using \<open>Cong B P D P\<close> not_cong_2143 by blast
    hence "B InCircle A B" 
      by (simp add: onc212 onc__inc)
    have "B InCircle C D" 
      using InCircle_def \<open>Bet C P D\<close> \<open>Cong P B P D\<close> triangle_inequality by blast
    then obtain Z0 where "Z0 OnCircle A B" and "Z0 OnCircle C D" 
      using assms(1) circle_circle_bis_def \<open>D InCircle A B\<close> onc212 by blast
    then obtain Z where "Z OnCircle A B" and "Z OnCircle C D" and "Coplanar A C U Z" 
      using circle_circle_cop by blast
    have "Col U V Z" 
    proof -
      {
        assume "A = C" 
        hence "A A Reflect U V" 
          using \<open>A C Reflect U V\<close> by auto
        hence "Col A U V" 
          by (simp add: l10_8)
        hence False 
          by (metis False \<open>\<not> Col U V B\<close> assms(2) assms(3) assms(4) bet_col 
              col_permutation_1 col_transitivity_1)
      }
      moreover have "Cong A B C D" 
        by (meson \<open>B D Reflect U V\<close> \<open>A C Reflect U V\<close> l10_10 not_cong_3412)
      hence "Cong A B C Z" 
        using OnCircle_def \<open>Z OnCircle C D\<close> cong_symmetry cong_transitivity by blast
      hence "Cong A Z C Z" 
        using OnCircle_def \<open>Z OnCircle A B\<close> cong_inner_transitivity onc_sym by blast
      moreover 
      { 
        assume "Col C U A" 
        have "A = C \<longrightarrow> False" 
          using calculation(1) by blast
        moreover 
        {
          assume "A \<noteq> C" 
          have "A C ReflectL U V" 
            using assms(3) \<open>A C Reflect U V\<close> is_image_is_image_spec by blast
          hence "U ReflectLAt A C U V" 
            by (meson \<open>A \<noteq> C\<close> \<open>Col C U A\<close> image_image_in not_col_distincts 
                not_col_permutation_3)
          hence "U V Perp C A \<or> C = A" 
            using ReflectLAt_def by blast
          hence "U V Perp C A" 
            using \<open>A \<noteq> C\<close> by blast
          hence "False" 
          proof (cases "A = U")
            case True
            then show ?thesis 
              using False \<open>\<not> Col U V B\<close> assms(2) assms(4) bet_col colx 
                not_col_distincts by blast
          next
            case False
            have "U A Perp U V" 
              by (metis False Perp_cases \<open>A \<noteq> C\<close> \<open>Col C U A\<close> \<open>U V Perp C A \<or> C = A\<close>
                  not_col_permutation_1 perp_col1)
            thus ?thesis 
              using assms(5) perp_per_2 by auto
          qed
        }
        ultimately have False 
          by blast
      }
      hence "\<not> Col C U A"
        by blast
      have "Coplanar C U A V" 
        using \<open>A C Reflect U V\<close> coplanar_perm_8 reflect__coplanar by blast
      have "Coplanar C U A Z" 
        by (simp add: \<open>Coplanar A C U Z\<close> coplanar_perm_8)
      hence "Coplanar U A V Z" 
        using \<open>Coplanar C U A V\<close> \<open>\<not> Col C U A\<close> coplanar_trans_1 by blast
      hence "Coplanar U V A Z" 
        using ncoplanar_perm_2 by blast
      ultimately show ?thesis 
        using \<open>A C Reflect U V\<close> cong_cop_image__col by blast
    qed
    thus ?thesis 
      using \<open>Z OnCircle A B\<close> by blast
  qed
qed

lemma circle_circle_bis__one_point_line_circle:
  assumes "circle_circle_bis" 
  shows "one_point_line_circle" 
proof -
  {
    fix A B U V P
    assume "Col U V P" and "U \<noteq> V" and "Bet A P B"
    have "\<exists> Z. Col U V Z \<and> Z OnCircle A B" 
    proof (cases "Per A U V")
      case True
      hence "\<not> Per A V U" 
        using \<open>U \<noteq> V\<close> l8_7 by blast
      then obtain Z where "Col V U Z \<and> Z OnCircle A B" 
        using Col_cases \<open>Bet A P B\<close> \<open>Col U V P\<close> \<open>U \<noteq> V\<close> 
          circle_circle_bis__one_point_line_circle_aux assms(1) by blast
      thus ?thesis 
        using Col_cases by blast
    next
      case False
      thus ?thesis 
        using \<open>Bet A P B\<close> \<open>Col U V P\<close> \<open>U \<noteq> V\<close> assms(1)
          circle_circle_bis__one_point_line_circle_aux by auto
    qed
  }
  thus ?thesis 
    using one_point_line_circle_def by blast
qed

lemma circle_circle__circle_circle_two_R1 :
  assumes "circle_circle" 
  shows "circle_circle_two" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "Q OnCircle C D" and
      "P InCircle A B" and "Q OutCircle A B"
    have "\<exists> Z1 Z2. Z1 OnCircle A B \<and> Z1 OnCircle C D \<and>
    Z2 OnCircle A B \<and> Z2 OnCircle  C D \<and>
    ((P InCircleS A B \<and> Q OutCircleS A B)\<longrightarrow>Z1 \<noteq> Z2)" 
    proof (cases "A = C")
      case True
      have "Cong A B A D" 
      proof -
        have "A B Le A D" 
        proof -
          have "A B Le A Q" 
            using OutCircle_def \<open>Q OutCircle A B\<close> by blast
          moreover have "Cong A B A B" 
            by (simp add: cong_reflexivity)
          moreover have "Cong A Q A D" 
            using OnCircle_def True \<open>Q OnCircle C D\<close> by blast
          ultimately show ?thesis 
            using l5_6 by blast
        qed
        moreover have "A D Le A B" 
        proof -
          have "A P Le A B" 
            using InCircle_def \<open>P InCircle A B\<close> by blast
          moreover have "Cong A P A D" 
            using OnCircle_def True \<open>P OnCircle C D\<close> by auto
          moreover have "Cong A B A B" 
            by (simp add: cong_reflexivity)
          ultimately show ?thesis 
            using l5_6 by blast
        qed
        ultimately show ?thesis 
          using le_anti_symmetry by blast
      qed
      have "P OnCircle A B" 
        using EqC_def True \<open>Cong A B A D\<close> \<open>P OnCircle C D\<close> eqc_chara_2 by presburger
      moreover have "P OnCircle C D" 
        using \<open>P OnCircle C D\<close> by auto
      moreover have "(P InCircleS A B \<and> Q OutCircleS A B)\<longrightarrow>P \<noteq> P" 
        using calculation(1) onc__outc outc__nincs by blast
      ultimately show ?thesis 
        by blast
    next
      case False
      obtain Z1 where "Z1 OnCircle A B" and "Z1 OnCircle C D" 
        using \<open>P InCircle A B\<close> \<open>P OnCircle C D\<close> \<open>Q OnCircle C D\<close> \<open>Q OutCircle A B\<close> 
          assms circle_circle_def by blast
      obtain Z2 where "Z1 Z2 Reflect A C" 
        using l10_6_existence by fastforce
      have "Cong Z1 C Z2 C" 
        by (metis False \<open>Z1 Z2 Reflect A C\<close> image_triv is_image_col_cong is_image_rev l10_8)
      have "Cong Z1 A Z2 A" 
      proof (rule is_image_col_cong [where ?A="A" and ?B="C"])
        show "A \<noteq> C" 
          by (simp add: False)
        show "Z1 Z2 Reflect A C" 
          by (simp add: \<open>Z1 Z2 Reflect A C\<close>)
        show "Col A C A" 
          by (simp add: col_trivial_3)
      qed
      have "Z2 OnCircle A B" 
        by (meson OnCircle_def \<open>Cong Z1 A Z2 A\<close> \<open>Z1 OnCircle A B\<close> 
            cong_transitivity not_cong_4321)
      moreover have "Z2 OnCircle  C D" 
        by (meson OnCircle_def \<open>Cong Z1 C Z2 C\<close> \<open>Z1 OnCircle C D\<close> 
            cong_transitivity not_cong_4321)
      moreover 
      {
        assume "P InCircleS A B" and "Q OutCircleS A B"
        assume "Z1 = Z2"
        {
          assume "Bet A C Z1" 
          have "Cong C Q C Z1" 
            using \<open>Q OnCircle C D\<close> \<open>Z1 OnCircle C D\<close> onc2__cong by blast
          hence "A Q Le A Z1" 
            using \<open>Bet A C Z1\<close> triangle_inequality by auto
          hence "A Q Le A B" 
            using InCircle_def \<open>Z1 OnCircle A B\<close> le_transitivity onc__inc by blast
          hence False 
            using InCircle_def \<open>Q OutCircleS A B\<close> outcs__ninc_1 by blast
        }
        moreover 
        {
          assume "C Out A Z1"
          have "Cong C P C Z1" 
            using \<open>P OnCircle C D\<close> \<open>Z1 OnCircle C D\<close> onc2__cong by force
          hence "A Z1 Le A P" 
            using \<open>C Out A Z1\<close> triangle_reverse_inequality by blast
          hence "A B Le A P" 
            using OutCircle_def \<open>Z1 OnCircle A B\<close> le_transitivity onc__outc by blast
          hence False 
            using InCircle_def \<open>P InCircleS A B\<close> inc__outc outc__nincs_1 by blast
        }
        moreover 
        { 
          assume "\<not> Col A C Z1"
          have "Col Z1 A C" 
            using l10_8 \<open>Z1 = Z2\<close> \<open>Z1 Z2 Reflect A C\<close> by blast
          hence False 
            using NCol_perm \<open>\<not> Col A C Z1\<close> by blast
        }
        ultimately have False 
          using not_bet_out by blast 
      }
      ultimately show ?thesis 
        using \<open>Z1 OnCircle A B\<close> \<open>Z1 OnCircle C D\<close> by blast
    qed
  }
  thus ?thesis 
    using circle_circle_two_def by blast
qed

lemma circle_circle__circle_circle_two_R2 :
  assumes "circle_circle_two"
  shows "circle_circle" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "Q OnCircle C D" and 
      "P InCircle A B" and "Q OutCircle A B"
    then obtain Z1 Z2 where "Z1 OnCircle A B \<and> Z1 OnCircle C D \<and>
    Z2 OnCircle A B \<and> Z2 OnCircle  C D \<and>
    ((P InCircleS A B \<and> Q OutCircleS A B) \<longrightarrow> Z1 \<noteq> Z2)" 
      using assms circle_circle_two_def by blast
    have "Z1 OnCircle A B" 
      by (simp add: \<open>Z1 OnCircle A B \<and> Z1 OnCircle C D \<and> Z2 OnCircle A B \<and> 
                     Z2 OnCircle C D \<and> (P InCircleS A B \<and> Q OutCircleS A B \<longrightarrow> Z1 \<noteq> Z2)\<close>)
    moreover have "Z1 OnCircle C D" 
      by (simp add: \<open>Z1 OnCircle A B \<and> Z1 OnCircle C D \<and> Z2 OnCircle A B \<and> 
                     Z2 OnCircle C D \<and> (P InCircleS A B \<and> Q OutCircleS A B \<longrightarrow> Z1 \<noteq> Z2)\<close>)
    ultimately have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
      by blast
  }
  thus ?thesis 
    using circle_circle_def by blast
qed

lemma circle_circle__circle_circle_two :
  shows "circle_circle \<longleftrightarrow> circle_circle_two" 
  using circle_circle__circle_circle_two_R1 circle_circle__circle_circle_two_R2 by blast

lemma euclid_22_aux:
  assumes "A B C D SumS E' F'" and
    "C D E F SumS A' B'" and
    "E F Le E' F'" and
    "A B Le A' B'" and
    "A Out B C1" and
    "Cong A C1 C D" and
    "Bet B A C2" and
    "Cong A C2 C D" and
    "B Out A E1" and
    "Cong B E1 E F"
  shows "Bet C1 E1 C2" 
proof -
  have "Bet C1 A C2" 
    using assms(5) assms(7) bet_out__bet by blast
  have "Col C1 E1 C2" 
    by (metis Out_def assms(5) assms(7) assms(9) bet_col col3 not_col_permutation_4 out_col)
  moreover 
  {
    assume "E1 Out C1 C2" 
    {
      assume "Bet E1 C1 C2" 
      have "Bet A C1 E1" 
        using \<open>Bet C1 A C2\<close> \<open>Bet E1 C1 C2\<close> between_inner_transitivity 
          between_symmetry by blast
      have "Bet A E1 B" 
        by (meson Out_def \<open>Bet A C1 E1\<close> assms(5) assms(9) between_inner_transitivity 
            between_symmetry not_bet_and_out)
      have "A' B' Lt A B" 
      proof -
        have "C D Lt A E1" 
          by (metis Out_def \<open>Bet A C1 E1\<close> \<open>E1 Out C1 C2\<close> assms(6) bet__lt1213 
              cong2_lt__lt cong_reflexivity)
        moreover have "E F Le E1 B" 
          using Cong_cases assms(10) cong__le3412 by blast
        moreover have "C D E F SumS A' B'" 
          by (simp add: assms(2))
        moreover have "A E1 E1 B SumS A B" 
          by (simp add: \<open>Bet A E1 B\<close> bet__sums)
        ultimately show ?thesis 
          using le_lt12_sums2__lt by blast
      qed
      hence False 
        using assms(4) lt__nle by force
    }
    moreover {
      assume "Bet E1 C2 C1"
      hence "Bet A C2 E1" 
        using Bet_cases \<open>Bet C1 A C2\<close> between_exchange3 by blast
      hence "Bet B C2 E1" 
        by (metis \<open>Bet E1 C2 C1\<close> assms(6) assms(7) assms(8) calculation cong_diff_4 
            cong_identity outer_transitivity_between2)
      have "B C2 Lt B E1" 
        using Out_def \<open>Bet B C2 E1\<close> \<open>E1 Out C1 C2\<close> bet__lt1213 by auto
      moreover have "Cong B C2 E' F'" 
        using SumS_def assms(1) assms(7) assms(8) cong_pseudo_reflexivity 
          cong_reflexivity sums2__cong56 by blast
      ultimately have "E' F' Lt E F" 
        using assms(10) cong2_lt__lt by blast
      hence False 
        by (simp add: assms(3) le__nlt)
    }
    ultimately have False 
      using Out_def \<open>E1 Out C1 C2\<close> by presburger
  }
  ultimately show ?thesis 
    using not_out_bet by blast
qed

lemma circle_circle_bis__euclid_22:
  assumes "circle_circle_bis"
  shows "euclid_s_prop_1_22"
proof -
  {
    fix A B C D E F A' B' C' D' E' F'
    assume "A B C D SumS E' F'" and "A B E F SumS C' D'" and "C D E F SumS A' B'" and
      "E F Le E' F'" and "C D Le C' D'" and "A B Le A' B'"
    have "\<exists> R. Cong A B A B \<and> Cong A R C D \<and> Cong B R E F" 
    proof (cases "A = B")
      case True
      obtain P where "Cong A P C D" 
        using segment_construction_0 by blast
      have "C D Le E F" 
        using True \<open>A B E F SumS C' D'\<close> \<open>C D Le C' D'\<close> cong_reflexivity l5_6
          not_cong_3412 sums__cong2345 by blast
      moreover have "E F Le C D" 
        using True \<open>A B C D SumS E' F'\<close> \<open>E F Le E' F'\<close> cong_reflexivity l5_6 
          not_cong_3412 sums__cong2345 by blast
      ultimately have "Cong C D E F" 
        using le_anti_symmetry by auto
      hence "Cong A P E F" 
        using \<open>Cong A P C D\<close> cong_transitivity by blast
      hence "Cong B P E F" 
        using True by auto
      thus ?thesis 
        using True \<open>Cong A P C D\<close> cong_pseudo_reflexivity by blast
    next
      case False
      hence "A \<noteq> B" 
        by simp
      show ?thesis
      proof (cases "C = D")
        case True
        have "B A Le E F" 
          using True \<open>A B Le A' B'\<close> \<open>C D E F SumS A' B'\<close> cong_pseudo_reflexivity
            l5_6 not_cong_3412 sums__cong2345 by blast
        moreover have "E F Le B A" 
          using True \<open>A B C D SumS E' F'\<close> \<open>E F Le E' F'\<close> cong_reflexivity
            l5_6 not_cong_4312 sums__cong1245 by blast
        ultimately have "Cong B A E F" 
          using le_anti_symmetry by auto
        thus ?thesis 
          using True cong_reflexivity cong_trivial_identity by blast
      next
        case False
        hence "C \<noteq> D" 
          by simp
        show ?thesis 
        proof (cases "E = F")
          case True
          thus ?thesis 
            by (metis \<open>A B C D SumS E' F'\<close> \<open>A B E F SumS C' D'\<close> \<open>A B Le A' B'\<close> 
                \<open>C D E F SumS A' B'\<close> \<open>C D Le C' D'\<close> cong_reflexivity le2_sums2__cong34 
                le2_sums2__le12 le_trivial sums123312 sums_sym)
        next
          case False
          hence "E \<noteq> F" 
            by simp
          obtain C1 where "A Out B C1" and "Cong A C1 C D" 
            using segment_construction_3 \<open>A \<noteq> B\<close> \<open>C \<noteq> D\<close> by force
          obtain E1 where "B Out A E1" and "Cong B E1 E F" 
            using segment_construction_3 \<open>A \<noteq> B\<close> \<open>E \<noteq> F\<close> by metis
          obtain C2 where "Bet B A C2" and "Cong A C2 C D" 
            using segment_construction by blast
          obtain E2 where "Bet A B E2" and "Cong B E2 E F"   
            using segment_construction by blast
          have "Bet C1 E1 C2" using euclid_22_aux [where ?A="A" and ?B="B" and 
                ?C="C" and ?D="D" and ?E="E" and ?F="F" and
                ?A'="A'" and ?B'="B'" and ?E'="E'" and ?F'="F'"]   
            using \<open>A B C D SumS E' F'\<close> \<open>A B Le A' B'\<close> \<open>A Out B C1\<close> \<open>B Out A E1\<close> 
              \<open>Bet B A C2\<close> \<open>C D E F SumS A' B'\<close> \<open>Cong A C1 C D\<close> \<open>Cong A C2 C D\<close> 
              \<open>Cong B E1 E F\<close> \<open>E F Le E' F'\<close> by blast
          have "Bet E1 C1 E2"  using euclid_22_aux [where ?A="B" and ?B="A" and 
                ?C="E" and ?D="F" and ?E="C" and ?F="D" and
                ?A'="B'" and ?B'="A'" and ?E'="C'" and ?F'="D'" and ?C1.0="C1" 
                and ?C2.0="E2" and ?E1.0="C1"] 
            by (meson \<open>A B E F SumS C' D'\<close> \<open>A B Le A' B'\<close> \<open>A Out B C1\<close> \<open>B Out A E1\<close> 
                \<open>Bet A B E2\<close> \<open>C D E F SumS A' B'\<close> \<open>C D Le C' D'\<close> \<open>Cong A C1 C D\<close> \<open>Cong B E1 E F\<close> 
                \<open>Cong B E2 E F\<close> euclid_22_aux le_left_comm sums_left_comm sums_sym)
          have "E1 OnCircle B E1"
            by (simp add: onc212)
          moreover have "C1 OnCircle A C1"  
            by (simp add: onc212)
          moreover have "E1 InCircle A C1" 
          proof (rule bet_inc2__inc [where ?U="C1" and ?V="C2"])
            show "C1 InCircle A C1" 
              by (simp add: onc212 onc__inc)
            show "C2 InCircle A C1" 
              by (meson InCircle_def \<open>Cong A C1 C D\<close> \<open>Cong A C2 C D\<close> cong__le 
                  cong_inner_transitivity not_cong_3421)
            show "Bet C1 E1 C2" 
              using \<open>Bet C1 E1 C2\<close> by auto
          qed
          moreover have "C1  InCircle B E1" 
          proof (rule bet_inc2__inc [where ?U="E1" and ?V="E2"])
            show "E1 InCircle B E1" 
              by (simp add: onc212 onc__inc)
            show "E2 InCircle B E1" 
              by (meson InCircle_def \<open>Cong B E1 E F\<close> \<open>Cong B E2 E F\<close> cong__le3412 
                  cong_inner_transitivity not_cong_4321)
            show "Bet E1 C1 E2" 
              using \<open>Bet E1 C1 E2\<close> by auto
          qed
          ultimately obtain Z where "Z OnCircle A C1" and "Z OnCircle B E1" 
            using assms(1) circle_circle_bis_def by blast
          then show ?thesis 
            by (meson OnCircle_def \<open>Cong A C1 C D\<close> \<open>Cong B E1 E F\<close> 
                cong_reflexivity cong_transitivity)
        qed
      qed
    qed
    hence "\<exists> P Q R. (Cong P Q A B \<and> Cong P R C D \<and> Cong Q R E F)" 
      by blast
  }
  thus ?thesis
    using euclid_s_prop_1_22_def by blast
qed

lemma triangle_inequality1:
  assumes "A B B C SumS D E"
  shows "A C Le D E"
proof -
  obtain D' where "Bet A B D'" and "Cong B D' B C" 
    using segment_construction by blast
  have "A C Le A D'" 
    using \<open>Bet A B D'\<close> \<open>Cong B D' B C\<close> cong_symmetry triangle_inequality by blast
  moreover have "Cong A D' D E" 
    using SumS_def \<open>Bet A B D'\<close> \<open>Cong B D' B C\<close> assms cong_reflexivity sums2__cong56 by blast
  ultimately show ?thesis 
    using cong__le le_transitivity by blast
qed

lemma euclid_22__circle_circle:
  assumes "euclid_s_prop_1_22"
  shows "circle_circle" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "Q OnCircle C D" and "P InCircle A B" and "Q OutCircle A B"
    have "\<exists> X Y Z. Cong X Y A C \<and> Cong X Z A B \<and> Cong Y Z C D" 
    proof -
      obtain L1 R1 where "A B C D SumS L1 R1" 
        using ex_sums by blast
      obtain L2 R2 where "A C C D SumS L2 R2" 
        using ex_sums by blast
      obtain L3 R3 where "A C A B SumS L3 R3" 
        using ex_sums by blast
      have "C D Le L3 R3"
      proof - 
        obtain R S where "C A A P SumS R S"
          using ex_sums by blast
        have "C D Le R S" 
          by (metis Cong_cases OnCircle_def \<open>C A A P SumS R S\<close> \<open>P OnCircle C D\<close> 
              cong__le le_transitivity triangle_inequality1)
        moreover have "R S Le L3 R3"
          using le2_sums2__le [where ?A="C" and ?B="A" and ?C="A" and ?D="P" and 
              ?A'="A" and ?B'="C" and ?C'="A" and ?D'="B"] InCircle_def \<open>A C A B SumS L3 R3\<close> 
            \<open>C A A P SumS R S\<close> \<open>P InCircle A B\<close> le1221 by blast
        ultimately show ?thesis 
          using le_transitivity by blast
      qed
      moreover have "A C C Q SumS L2 R2" 
        by (meson OnCircle_def \<open>A C C D SumS L2 R2\<close> \<open>Q OnCircle C D\<close> 
            cong3_sums__sums cong_reflexivity onc_sym)
      hence "A Q Le L2 R2" 
        using triangle_inequality1 by auto
      hence "A B Le L2 R2" 
        using OutCircle_def \<open>Q OutCircle A B\<close> le_transitivity by blast
      moreover have "A C Le L1 R1" 
      proof -
        obtain R S where "A P P C SumS R S"
          using ex_sums by blast
        have "A C Le R S" 
          using \<open>A P P C SumS R S\<close> triangle_inequality1 by auto
        moreover have "R S Le L1 R1" 
          using le2_sums2__le [where ?A="A" and ?B="P" and ?C="P" and ?D="C" and 
              ?A'="A" and ?B'="B" and ?C'="C" and ?D'="D"] by (meson InCircle_def OnCircle_def 
              \<open>A B C D SumS L1 R1\<close> \<open>A P P C SumS R S\<close> \<open>P InCircle A B\<close> \<open>P OnCircle C D\<close> 
              cong__le not_cong_3421 onc_sym)
        ultimately show ?thesis 
          using le_transitivity by blast
      qed
      ultimately show ?thesis 
        using \<open>A B C D SumS L1 R1\<close> \<open>A C A B SumS L3 R3\<close> \<open>A C C D SumS L2 R2\<close> assms 
          euclid_s_prop_1_22_def by blast
    qed
    then obtain X Y Z where "Cong X Y A C" and "Cong X Z A B" and "Cong Y Z C D" 
      by blast
    have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
    proof (cases "A = C")
      case True
      then show ?thesis 
        using OnCircle_def \<open>\<exists>X Y Z. Cong X Y A C \<and> Cong X Z A B \<and> Cong Y Z C D\<close> 
          cong_identity cong_inner_transitivity by blast
    next
      case False
      hence "A \<noteq> C"
        by blast
      show ?thesis 
      proof (cases "A = B")
        case True
        then show ?thesis 
          using \<open>P InCircle A B\<close> \<open>P OnCircle C D\<close> inc__outc_1 inc_eq 
            inc_outc__onc by blast
      next
        case False
        hence "A \<noteq>B" 
          by simp
        have "X \<noteq> Z" 
          using False \<open>Cong X Z A B\<close> cong_reverse_identity by force
        have "X \<noteq> Y" 
          using \<open>A \<noteq> C\<close> \<open>Cong X Y A C\<close> cong_diff_3 by blast
        have "\<exists> Z0. Y X Z CongA C A Z0 \<and> Cong X Z A Z0"
        proof -
          obtain Z' where "Y X Z CongA C A Z'" 
            using \<open>A \<noteq> C\<close> \<open>X \<noteq> Y\<close> \<open>X \<noteq> Z\<close> angle_construction_3 by presburger
          obtain Z0 where "A Out Z' Z0" and "Cong A Z0 X Z" 
            by (metis \<open>X \<noteq> Z\<close> \<open>Y X Z CongA C A Z'\<close> conga_diff56 segment_construction_3)
          have "Y X Z CongA C A Z0" 
            by (metis \<open>A Out Z' Z0\<close> \<open>A \<noteq> C\<close> \<open>Y X Z CongA C A Z'\<close> not_conga 
                not_conga_sym out2__conga out_trivial)
          thus ?thesis 
            using \<open>Cong A Z0 X Z\<close> cong_symmetry by blast
        qed
        then obtain Z0 where "Y X Z CongA C A Z0" and "Cong X Z A Z0" 
          by blast
        then show ?thesis 
          by (meson OnCircle_def \<open>Cong X Y A C\<close> \<open>Cong X Z A B\<close> \<open>Cong Y Z C D\<close> 
              cong_inner_transitivity l11_49)
      qed
    qed
  }
  thus ?thesis 
    using circle_circle_def by blast
qed

theorem equivalent_variants_of_circle_circle:
  shows "(circle_circle \<longleftrightarrow> circle_circle_two) \<and>
    (circle_circle_two \<longleftrightarrow> circle_circle_bis) \<and>
    (circle_circle_bis \<longleftrightarrow> circle_circle_axiom)\<and>
    (circle_circle_axiom \<longleftrightarrow> euclid_s_prop_1_22)" 
proof -
  have "circle_circle \<longleftrightarrow> circle_circle_two" 
    using circle_circle__circle_circle_two by blast
  moreover have "circle_circle_two \<longleftrightarrow> circle_circle_bis" 
    using circle_circle__circle_circle_bis circle_circle__circle_circle_two 
      circle_circle_bis__euclid_22 euclid_22__circle_circle by blast
  moreover have "circle_circle_bis \<longleftrightarrow> circle_circle_axiom" 
    by (simp add: circle_circle_bis__circle_circle_axiom)
  moreover have "circle_circle_axiom \<longleftrightarrow> euclid_s_prop_1_22" 
    using circle_circle__circle_circle_bis circle_circle_bis__circle_circle_axiom 
      circle_circle_bis__euclid_22 euclid_22__circle_circle by blast
  ultimately show ?thesis 
    by blast
qed

theorem equivalent_variants_of_line_circle:
  shows "(segment_circle \<longleftrightarrow> one_point_line_circle) \<and> 
         (one_point_line_circle \<longleftrightarrow> two_points_line_circle)"
proof -
  have "segment_circle \<longrightarrow> one_point_line_circle" 
    by (simp add: segment_circle__one_point_line_circle)
  moreover have "one_point_line_circle \<longrightarrow> two_points_line_circle" 
    by (simp add: one_point_line_circle__two_points_line_circle)
  moreover have "two_points_line_circle \<longrightarrow> segment_circle" 
    by (simp add: one_point_line_circle__two_points_line_circle_R2 
        segment_circle__one_point_line_circle_R2)
  ultimately show ?thesis 
    by blast
qed

end
end

