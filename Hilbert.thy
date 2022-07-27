(* IsageoCoq2_R1

Hilbert.thy

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
theory Hilbert

imports
  Tarski_Neutral
  Tarski_2D

begin
  (*>*)

section "Hilbert - Geometry - neutral dimension less"

subsection "Axioms"

locale Hilbert_neutral_dimensionless_pre =
  fixes
    IncidL :: "TPoint \<Rightarrow> 'b \<Rightarrow> bool" and
    IncidP :: "TPoint \<Rightarrow> 'c \<Rightarrow> bool" and
    EqL ::"'b \<Rightarrow> 'b \<Rightarrow> bool" and
    EqP ::"'c \<Rightarrow> 'c \<Rightarrow> bool" and
    IsL ::"'b \<Rightarrow> bool" and
    IsP ::"'c \<Rightarrow> bool" and
    BetH ::"TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" and
    CongH::"TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" and
    CongaH::"TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" 

definition (in Hilbert_neutral_dimensionless_pre) ColH :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow>bool" where
  "ColH A B C \<equiv> (\<exists> l. IsL l \<and> IncidL A l \<and> IncidL B l \<and> IncidL C l)"

definition (in Hilbert_neutral_dimensionless_pre) IncidLP :: "'b\<Rightarrow>'c\<Rightarrow>bool" where
  "IncidLP l p \<equiv> IsL l \<and> IsP p \<and> (\<forall> A. IncidL A l \<longrightarrow> IncidP A p)"

definition (in Hilbert_neutral_dimensionless_pre) cut :: "'b\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "cut l A B \<equiv> IsL l \<and> \<not> IncidL A l \<and> \<not> IncidL B l \<and> (\<exists> I. IncidL I l \<and> BetH A I B)"

definition (in Hilbert_neutral_dimensionless_pre) outH :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "outH P A B \<equiv> BetH P A B \<or> BetH P B A \<or> (P \<noteq> A \<and> A = B)" 

definition (in Hilbert_neutral_dimensionless_pre) disjoint :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "disjoint A B C D \<equiv> \<not> (\<exists> P. BetH A P B \<and> BetH C P D)" 

definition (in Hilbert_neutral_dimensionless_pre) same_side :: "TPoint\<Rightarrow>TPoint\<Rightarrow>'b\<Rightarrow>bool" where
  "same_side A B l \<equiv> IsL l \<and> (\<exists> P. cut l A P \<and> cut l B P)" 

definition (in Hilbert_neutral_dimensionless_pre) same_side' :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" where
  "same_side' A B X Y \<equiv>
     X \<noteq> Y \<and>
     (\<forall> l::'b. (IsL l \<and> IncidL X l \<and> IncidL Y l) \<longrightarrow> same_side A B l)" 

locale Hilbert_neutral_dimensionless =  Hilbert_neutral_dimensionless_pre +
  fixes  PP PQ PR :: TPoint
  assumes 
    EqL_refl: "IsL l \<longrightarrow> EqL l l" and
    EqL_sym: "IsL l1 \<and> IsL l2 \<and> EqL l1 l2 \<longrightarrow> EqL l2 l1" and
    EqL_trans: "(EqL l1 l2 \<and> EqL l2 l3) \<longrightarrow> EqL l1 l3" and
    EqP_refl: "IsP p \<longrightarrow> EqP p p" and
    EqP_sym: "EqP p1 p2 \<longrightarrow> EqP p2 p1" and
    EqP_trans: "(EqP p1 p2 \<and> EqP p2 p3) \<longrightarrow> EqP p1 p3" and
IncidL_morphism: "(IsL l \<and> IsL m \<and>  IncidL P l \<and> EqL l m) \<longrightarrow> IncidL P m" and
IncidP_morphism: "(IsP p \<and> IsP q \<and> IncidP M p \<and> EqP p q) \<longrightarrow> IncidP M q" and
Is_line:"IncidL P l \<longrightarrow> IsL l" and
Is_plane:"IncidP P p \<longrightarrow> IsP p" 
assumes
    (** Group I Incidence *)
    line_existence: "A \<noteq> B \<longrightarrow> (\<exists> l. IsL l \<and> ( IncidL A l \<and> IncidL B l))" and
    line_uniqueness: "A \<noteq> B \<and> IsL l \<and> IsL m \<and>
     IncidL A l \<and> IncidL B l \<and> IncidL A m \<and> IncidL B m \<longrightarrow>
     EqL l m" and
    two_points_on_line: "\<forall> l. IsL l \<longrightarrow> (\<exists> A B. IncidL A l \<and> IncidL B l \<and> A \<noteq> B)" 
  assumes 
    lower_dim_2: "PP \<noteq> PQ \<and> PQ \<noteq> PR \<and> PP \<noteq> PR \<and> \<not> ColH PP PQ PR" and
(*lower_dim_2: "\<exists> PP PQ PR. PP \<noteq> PQ \<and> PQ \<noteq> PR \<and> PP \<noteq> PR \<and> \<not> ColH PP PQ PR" and*)
    plan_existence: "\<forall> A B C. ((\<not> ColH A B C) \<longrightarrow> (\<exists> p. IsP p \<and> IncidP A p \<and> IncidP B p \<and> IncidP C p))" and
    one_point_on_plane: "\<forall> p. \<exists> A. IsP p \<longrightarrow> IncidP A p" and
    plane_uniqueness: "\<not> ColH A B C \<and> IsP p \<and> IsP q \<and>
     IncidP A p \<and> IncidP B p \<and> IncidP C p \<and> IncidP A q \<and> IncidP B q \<and> IncidP C q \<longrightarrow>
     EqP p q"  and
    line_on_plane: "\<forall> A B l p. A \<noteq> B \<and> IsL l \<and> IsP p \<and>
     IncidL A l \<and> IncidL B l \<and> IncidP A p \<and> IncidP B p \<longrightarrow> IncidLP l p"
  assumes 
    between_diff: "BetH A B C \<longrightarrow> A \<noteq> C" and
    between_col: "BetH A B C \<longrightarrow> ColH A B C" and
    between_comm: "BetH A B C \<longrightarrow> BetH C B A" and
    between_out: " A \<noteq> B \<longrightarrow> (\<exists> C. BetH A B C)" and
    between_only_one: "BetH A B C \<longrightarrow> \<not> BetH B C A" and
    pasch: "\<not> ColH A B C \<and> IsL l \<and> IsP p \<and>
     IncidP A p \<and> IncidP B p \<and> IncidP C p \<and> IncidLP l p \<and> \<not> IncidL C l \<and>
 (cut l A B)
\<longrightarrow>
     (cut l A C) \<or> (cut l B C)"
  assumes
cong_permr: "CongH A B C D \<longrightarrow> CongH A B D C" and
    cong_existence: "\<And>A B A' P::TPoint. A \<noteq> B \<and> A' \<noteq> P \<and> IsL l \<and>
     IncidL A' l \<and> IncidL P l \<longrightarrow>
     (\<exists> B'. (IncidL B' l \<and> outH A' P B' \<and> CongH A' B' A B))" and
    cong_pseudo_transitivity:
    " CongH A B C D \<and> CongH A B E F \<longrightarrow> CongH C D E F" and
    addition : "
     ColH A B C \<and> ColH A' B' C' \<and>
     disjoint A B B C \<and> disjoint A' B' B' C' \<and>
     CongH A B A' B' \<and> CongH B C B' C' \<longrightarrow>
     CongH A C A' C'" and
    conga_refl: "\<not> ColH A B C \<longrightarrow> CongaH A B C A B C" and
    conga_comm : "\<not> ColH A B C \<longrightarrow> CongaH A B C C B A" and
    conga_permlr: "CongaH A B C D E F \<longrightarrow> CongaH C B A F E D" and
    conga_out_conga: "(CongaH A B C D E F \<and>
    outH B A A' \<and> outH B C C' \<and> outH E D D' \<and> outH E F F') \<longrightarrow>
    CongaH A' B C' D' E F'" and
    cong_4_existence: 
    " \<not> ColH P PO X \<and> \<not> ColH A B C \<longrightarrow>
 (\<exists> Y. (CongaH A B C X PO Y \<and> same_side' P Y PO X))" and
    cong_4_uniqueness:
    "\<not> ColH P PO X \<and> \<not> ColH A B C \<and>
     CongaH A B C X PO Y \<and> CongaH A B C X PO Y' \<and>
     same_side' P Y PO X \<and> same_side' P Y' PO X \<longrightarrow>
     outH PO Y Y'" and
    cong_5 : "\<not> ColH A B C \<and> \<not> ColH A' B' C' \<and>
     CongH A B A' B' \<and> CongH A C A' C' \<and>
     CongaH B A C B' A' C' \<longrightarrow>
     CongaH A B C A' B' C'"

section "Hilbert - Geometry - Neutral 2D"

subsection "Axioms: neutral 2D"

locale Hilbert_neutral_2D = Hilbert_neutral_dimensionless +
  assumes pasch_2D :
    "IsL l \<and>  \<not> ColH A B C \<and> \<not> IncidL C l \<and> cut l A B \<longrightarrow> (cut l A C \<or> cut l B C)"

section "Hilbert - Geometry - Neutral 3D"

subsection "Axioms: neutral 3D"

locale Hilbert_neutral_3D = Hilbert_neutral_dimensionless +
  fixes HS1 HS2 HS3 HS4 :: TPoint
  assumes plane_intersection: "IsP p \<and> IsP q \<and> IncidP A p \<and> IncidP A q \<longrightarrow> (\<exists> B. IncidP B p \<and> IncidP B q \<and> A \<noteq> B)" 
    and   lower_dim_3: "\<not> (\<exists> p. IsP p \<and> IncidP HS1 p \<and> IncidP HS2 p \<and> IncidP HS3 p \<and> IncidP HS4 p)"

section "Hilbert - Geometry - Euclidean"

subsection "Axioms: Euclidean"

definition (in Hilbert_neutral_dimensionless_pre) Para :: "'b \<Rightarrow> 'b \<Rightarrow>bool" where
  "Para l m \<equiv> IsL l \<and> IsL m \<and> (\<not>(\<exists> X. IncidL X l \<and> IncidL X m)) \<and> (\<exists> p. IncidLP l p \<and> IncidLP m p)"

locale Hilbert_euclidean = Hilbert_neutral_dimensionless +
  assumes euclid_uniqueness: "\<forall> l P m1 m2. IsL l \<and> IsL m1 \<and> IsL m2 \<and>
     \<not> IncidL P l \<and> Para l m1 \<and> IncidL P m1 \<and> Para l m2 \<and> IncidL P m2 \<longrightarrow>
     EqL m1 m2"

end