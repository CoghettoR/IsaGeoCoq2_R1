theory Desargues_Hessenberg

imports Tarski_Pappus

begin

section "Desargues - Hessenberg"

lemma (in Tarski_Euclidean) l13_15_1:
  assumes "\<not> Col A B C" and 
    "\<not> PO B Par A C" and 
    "Coplanar PO B A C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'"and
    "Col PO A A'" and
    "Col PO B B'" and
    "Col PO C C'"
  shows "B C Par B' C'" 
proof -
  {
    assume "Col B A' B'"
    hence False 
      using assms(4) par_strict_not_col_2 by auto
  }
  {
    assume "Col A A' B'" 
    hence False 
      using assms(4) col_permutation_1 par_strict_not_col_3 by blast
  }
  have "B \<noteq> PO" 
    using assms(4) assms(6) col_permutation_4 par_strict_not_col_1 by blast
  have "A \<noteq> PO" 
    using assms(5) assms(8) par_strict_not_col_4 by blast
  have "\<not> Col A' A C" 
    using assms(5) col_permutation_1 par_strict_not_col_1 by blast
  have "C \<noteq> PO" 
    using Col_cases \<open>\<not> Col A' A C\<close> assms(6) by blast
  have "\<not> Col PO A B" 
    by (metis \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> \<open>Col B A' B' \<Longrightarrow> False\<close> assms(6) assms(7) col3 col_trivial_3)
  {
    assume "Col A' B' C'"
    hence "A' C' Par A B" 
      by (metis assms(1) assms(4) assms(5) par_id par_strict_col_par_strict 
          par_strict_neq2 par_strict_symmetry par_strict_trans)
    hence "A C Par A B" 
      using \<open>A' C' Par A B\<close> assms(5) par_not_par par_strict_par by blast
    hence False 
      using assms(1) par_id_3 by auto
  }
  show ?thesis
  proof (cases "Col PO B C")
    case True
    thus ?thesis 
      by (metis Par_def \<open>B \<noteq> PO\<close> \<open>C \<noteq> PO\<close> \<open>Col A' B' C' \<Longrightarrow> False\<close> assms(1) assms(7) 
          assms(8) col_transitivity_1 col_trivial_2 not_col_permutation_2)
  next
    case False
    hence "\<not> Col PO B C"
      by auto
    have "B' \<noteq> PO" 
      using Col_cases \<open>Col A A' B' \<Longrightarrow> False\<close> assms(6) by blast
    have "A' \<noteq> PO" 
      using Col_cases \<open>Col B A' B' \<Longrightarrow> False\<close> assms(7) by blast
    have "\<not> Col A A' C'" 
      using assms(5) col_permutation_1 par_strict_not_col_3 by blast
    have "C' \<noteq> PO" 
      using Col_cases \<open>\<not> Col A A' C'\<close> assms(6) by blast
    have "\<not> Col PO A' B'" 
      by (meson \<open>B' \<noteq> PO\<close> \<open>Col B A' B' \<Longrightarrow> False\<close> assms(7) col2__eq col_permutation_2)
    have "\<not> Col PO A' C'" 
      by (metis \<open>A' \<noteq> PO\<close> \<open>\<not> Col A A' C'\<close> assms(6) col2__eq col_permutation_1)
    have "\<not> Col B' A B" 
      using assms(4) col_permutation_1 par_strict_not_col_4 by blast
    have "\<not> Col A' A B" 
      using assms(4) col_permutation_1 par_strict_not_col_1 by blast
    have "\<exists> C D. C \<noteq> D \<and> PO B Par C D \<and> Col A C D" 
      by (metis \<open>B \<noteq> PO\<close> col_trivial_1 par_distinct parallel_existence1)
    then obtain X Y where "X \<noteq> Y" and "PO B Par X Y" and "Col A X Y" 
      by blast
    have "Coplanar PO B X A" 
      using \<open>Col A X Y\<close> \<open>PO B Par X Y\<close> \<open>X \<noteq> Y\<close> col_cop__cop 
        col_permutation_1 par_cong_cop by blast
    have "Coplanar PO B Y A" 
      using NCol_perm \<open>Col A X Y\<close> \<open>PO B Par X Y\<close> \<open>X \<noteq> Y\<close> col_cop__cop 
        ncoplanar_perm_1 par_cong_cop by blast
    have "\<exists> L. Col L X Y \<and> Col L A' C'"
    proof -
      have "Coplanar X Y A' C'"    
      proof (rule coplanar_pseudo_trans [where ?P="PO" and ?Q="A" and ?R="B"])
        show "\<not> Col PO A B" 
          by (simp add: \<open>\<not> Col PO A B\<close>)
        show "Coplanar PO A B X" 
          using \<open>Coplanar PO B X A\<close> coplanar_perm_4 by presburger
        show "Coplanar PO A B Y" 
          using \<open>Coplanar PO B Y A\<close> coplanar_perm_4 by blast
        show "Coplanar PO A B A'" 
          using assms(6) ncop__ncols by blast
        show "Coplanar PO A B C'" 
          by (metis \<open>C \<noteq> PO\<close> assms(3) assms(8) col_cop2__cop coplanar_perm_2 ncop_distincts)
      qed
      moreover {
        assume "X Y Par A' C'"
        have "PO B Par X Y" 
          using \<open>PO B Par X Y\<close> by auto
        moreover have "X Y Par A C" 
          using \<open>X Y Par A' C'\<close> assms(5) not_par_one_not_par par_strict_par by blast
        ultimately have False 
          using assms(2) par_not_par by blast
      }
      ultimately show ?thesis 
        using cop_npar__inter_exists by blast
    qed
    then obtain L where "Col L X Y" and "Col L A' C'" 
      by blast
    moreover have "B C Par B' C'"         
    proof -
      have "A \<noteq> L" 
        using \<open>Col L A' C'\<close> \<open>\<not> Col A A' C'\<close> by auto
      have "A L Par PO B'" 
        by (metis Par_def \<open>A \<noteq> L\<close> \<open>B \<noteq> PO\<close> \<open>B' \<noteq> PO\<close> \<open>Col A X Y\<close> 
            \<open>Col L X Y\<close> \<open>PO B Par X Y\<close> \<open>X \<noteq> Y\<close> assms(7) not_par_not_col 
            not_par_one_not_par par_trans)
      have "L A Par PO B"
      proof (cases "X = L")
        case True
        show ?thesis 
        proof (rule par_col_par_2 [where ?B="Y"])
          show "L \<noteq> A" 
            using \<open>A \<noteq> L\<close> by auto
          show "Col L Y A" 
            using Col_cases True \<open>Col A X Y\<close> by blast
          show "L Y Par PO B" 
            using Par_cases True \<open>PO B Par X Y\<close> by blast
        qed
      next
        case False
        then show ?thesis 
          by (metis \<open>A L Par PO B'\<close> \<open>B \<noteq> PO\<close> assms(7) not_col_distincts 
              par_col2_par_bis par_left_comm)
      qed
      {
        assume "X Y Par PO C"
        hence "PO B Par PO C" 
          using \<open>PO B Par X Y\<close> par_trans by blast
        hence False 
          using False par_id by auto
      }
      have "Coplanar X Y PO C" 
        using coplanar_pseudo_trans 
        by (meson \<open>Coplanar PO B X A\<close> \<open>Coplanar PO B Y A\<close> \<open>\<not> Col PO A B\<close> assms(3) 
            coplanar_perm_1 ncop_distincts not_col_permutation_5)
      hence "\<exists> X0. Col X0 X Y \<and> Col X0 PO C" 
        using \<open>X Y Par PO C \<Longrightarrow> False\<close> cop_npar__inter_exists by blast
      then obtain M where "Col M X Y" and "Col M PO C"
        by blast
      hence "A \<noteq> M" 
        by (metis Col_cases \<open>A \<noteq> PO\<close> \<open>\<not> Col A' A C\<close> assms(6) colx not_col_distincts)
      have "PO B Par A M" 
        by (meson Col_cases \<open>A \<noteq> M\<close> \<open>Col A X Y\<close> \<open>Col M X Y\<close> \<open>PO B Par X Y\<close> par_col2_par)
      have "L \<noteq> A'" 
        by (metis \<open>A L Par PO B'\<close> \<open>Col A A' B' \<Longrightarrow> False\<close> assms(6) not_col_distincts 
            not_par_not_col not_strict_par par_id_2)
      {
        assume "L B' Par A' B'"
        {
          assume "L B' ParStrict A' B'"
          hence False 
            using col_trivial_3 par_strict_not_col_2 by blast
        }
        hence False 
          using Par_def \<open>Col A' B' C' \<Longrightarrow> False\<close> \<open>L B' Par A' B'\<close> \<open>L \<noteq> A'\<close> calculation(2) 
            col_transitivity_2 by blast
      }
      {
        assume "A B Par L B'" 
        hence False using par_not_par 
          using \<open>L B' Par A' B' \<Longrightarrow> False\<close> assms(4) par_strict_par par_symmetry by blast
      }
      have "Coplanar A B L B'" 
        by (metis \<open>B \<noteq> PO\<close> \<open>L A Par PO B\<close> assms(7) col_par col_trivial_3 coplanar_perm_8 
            ncop__ncols par_cong_cop par_not_par)
      then obtain N where "Col N A B" and "Col N L B'" 
        using \<open>A B Par L B' \<Longrightarrow> False\<close> cop_npar__inter_exists by blast
      have "A L ParStrict PO B'" 
        by (metis NCol_cases Par_def \<open>A L Par PO B'\<close> \<open>A \<noteq> PO\<close> assms(4) assms(6) 
            col_transitivity_2 par_strict_comm par_strict_not_col_2)
      hence "A \<noteq> N" 
        using \<open>Col N L B'\<close> par_strict_not_col_4 by blast
      hence "A N Par A' B'" 
        by (metis \<open>B \<noteq> PO\<close> \<open>Col N A B\<close> \<open>\<not> Col PO A B\<close> assms(4) 
            col_par par_id_3 par_left_comm par_not_par par_reflexivity par_strict_par)
      have "PO N Par L A'" 
      proof (cases "A PO Par N L")
        case True
        hence "A PO ParStrict N L" 
          using Par_strict_perm \<open>A L ParStrict PO B'\<close> \<open>Col N L B'\<close> 
            par_not_col_strict par_strict_not_col_2 by blast
        show ?thesis
        proof (rule l13_14 [where ?PO="A" and ?O'="N" and ?C="A'" and ?C'="N"])
          show "A PO ParStrict N L" 
            using \<open>A PO ParStrict N L\<close> by auto
          show "Col A PO A'" 
            using Col_cases assms(6) by blast
          show "Col A A' A'" 
            using not_col_distincts by blast
          show "Col A PO A'" 
            using \<open>Col A PO A'\<close> by blast
          show "Col N L N" 
            using not_col_distincts by auto
          show "Col N N N"    
            using not_col_distincts by auto
          show "Col N L N"    
            using not_col_distincts by auto
          show "PO N Par L A'" 
            by (meson \<open>A L Par PO B'\<close> \<open>A N Par A' B'\<close> \<open>A PO ParStrict N L\<close> \<open>Col A PO A'\<close> 
                \<open>Col N L B'\<close> l13_14 not_col_distincts par_left_comm par_symmetry)
          show "A' N Par N A'" 
            by (metis Par_cases \<open>Col N A B\<close> \<open>\<not> Col A' A B\<close> par_reflexivity)
        qed
      next
        case False
        hence "\<not> A PO Par N L" 
          by blast
        have "N \<noteq> L" 
          using \<open>A L ParStrict PO B'\<close> \<open>Col N A B\<close> assms(7) 
            not_col_permutation_3 not_col_permutation_4 par_not_col by blast
        have "L \<noteq> B'" 
          using Col_cases \<open>Col A' B' C' \<Longrightarrow> False\<close> calculation(2) by blast
        have "Col L B' N" 
          using Col_cases \<open>Col N L B'\<close> by blast
        have "Coplanar A PO L B'" 
          using \<open>A L Par PO B'\<close> coplanar_perm_2 par_cong_cop by blast
        hence "Coplanar A PO N L" 
          using col_cop__cop \<open>Col L B' N\<close> \<open>L \<noteq> B'\<close> coplanar_perm_1 by blast
        then obtain P where "Col P A PO" and "Col P N L" 
          using False cop_npar__inter_exists by blast
        have "PO N Par A' L" 
        proof -
          have "P \<noteq> L" 
            using \<open>A L ParStrict PO B'\<close> \<open>Col P A PO\<close> col_permutation_4 
              par_strict_not_col_1 by blast
          {
            assume "P = PO"
            hence "Col L A L" 
              using col_trivial_3 by blast
            moreover have "Col L PO B'"
            proof -
              have "Col L N PO" 
                using Col_cases \<open>Col P N L\<close> \<open>P = PO\<close> by blast
              moreover have "Col L N B'" 
                using Col_cases \<open>Col L B' N\<close> by blast
              ultimately show ?thesis 
                by (metis \<open>N \<noteq> L\<close> col_transitivity_1)
            qed
            ultimately have  False             
              using \<open>A L ParStrict PO B'\<close> par_strict_not_col_2 by auto
          }
          have "A \<noteq> P" 
            by (metis Col_cases \<open>A L ParStrict PO B'\<close> \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P N L\<close> 
                assms(7) col_transitivity_1 par_not_col)
          have "P \<noteq> N" 
            by (metis \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P A PO\<close> \<open>\<not> Col PO A B\<close> col3 col_trivial_2)
          have "A' \<noteq> P" 
            by (metis Par_def \<open>A N Par A' B'\<close> \<open>Col A A' B' \<Longrightarrow> False\<close> \<open>Col N L B'\<close> 
                \<open>Col P N L\<close> \<open>N \<noteq> L\<close> col_transitivity_1 not_col_permutation_2 par_strict_not_col_2)
          have "B' \<noteq> P" 
            using \<open>A L ParStrict PO B'\<close> \<open>Col P A PO\<close> col_permutation_2 
              par_strict_not_col_3 by blast
          have "\<not> Col P PO L" 
            by (metis Col_cases \<open>A L ParStrict PO B'\<close> \<open>Col P A PO\<close> \<open>P = PO \<Longrightarrow> False\<close> 
                col_transitivity_2 par_strict_not_col_1)
          show ?thesis 
          proof (rule l13_11 [where ?PO="P" and ?C="A" and ?C'="B'"],
              simp_all add: \<open>\<not> Col P PO L\<close> \<open>A \<noteq> P\<close> \<open>A' \<noteq> P\<close> \<open>B' \<noteq> P\<close> \<open>A L Par PO B'\<close>)
            show "Col P PO A'" 
              using Col_cases \<open>A \<noteq> PO\<close> \<open>Col P A PO\<close> assms(6) col2__eq by blast
            show "Col P A' A" 
              using Col_cases \<open>Col P A PO\<close> \<open>Col P PO A'\<close> \<open>P = PO \<Longrightarrow> False\<close> 
                col_transitivity_1 by blast
            show "N \<noteq> P" 
              using \<open>P \<noteq> N\<close> by auto
            show "Col P L N" 
              using Col_cases \<open>Col P N L\<close> by auto
            show "Col P N B'" 
              by (meson \<open>Col N L B'\<close> \<open>Col P L N\<close> \<open>Col P N L\<close> \<open>N \<noteq> L\<close> \<open>P \<noteq> L\<close> 
                  col_transitivity_1 colx)
            show "A' B' Par A N" 
              by (simp add: \<open>A N Par A' B'\<close> par_symmetry)
          qed
        qed
        then show ?thesis 
          using Par_cases by blast
      qed
      have "A' C' Par PO N" 
        by (metis Col_def \<open>L \<noteq> A'\<close> \<open>PO N Par L A'\<close> assms(5) between_trivial2 
            calculation(2) col_par not_par_one_not_par par_strict_not_col_2)
      hence "PO N Par A C" 
        using assms(5) par_strict_par par_symmetry par_trans by blast
      have "N M Par B C" 
      proof (cases "A N Par PO C")
        case True
        have "A N ParStrict PO C" 
          by (metis Col_cases Par_def Par_strict_cases True assms(5) assms(8) 
              col_transitivity_2 par_strict_not_col_3)
        have "N M Par C B" 
        proof (rule l13_14 [where ?PO="A" and ?C="A" and ?O'="PO" and ?C'="PO"],
            simp_all add: \<open>A N ParStrict PO C\<close>)
          show "Col A N B" 
            using Col_cases \<open>Col N A B\<close> by blast
          show "Col A B A" 
            using not_col_distincts by blast
          show "Col A N A" 
            using not_col_distincts by blast
          show "Col PO C M" 
            using Col_cases \<open>Col M PO C\<close> by blast
          show "Col PO M PO" 
            using not_col_distincts by blast
          show "Col PO C PO" 
            by (simp add: col_trivial_3)
          show "N PO Par C A" 
            using Par_cases \<open>PO N Par A C\<close> by blast
          show "B PO Par M A" 
            using Par_cases \<open>PO B Par A M\<close> by blast
        qed
        thus ?thesis 
          using Par_cases by blast
      next
        case False
        hence "\<not> A N Par PO C"
          by blast
        have "Coplanar A N PO C" 
          using \<open>PO N Par A C\<close> coplanar_perm_14 par_cong_cop by blast
        then obtain P where "Col P A N" and "Col P PO C" 
          using False cop_npar__inter_exists by blast
        have "B \<noteq> P" 
          using Col_cases \<open>Col P PO C\<close> \<open>\<not> Col PO B C\<close> by blast
        have "A \<noteq> P" 
          by (metis Col_cases \<open>A \<noteq> PO\<close> \<open>Col P PO C\<close> \<open>\<not> Col A' A C\<close> assms(6) 
              colx not_col_distincts)
        have "M \<noteq> P" 
          by (metis \<open>A \<noteq> N\<close> \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> \<open>Col N A B\<close> \<open>Col P A N\<close> 
              \<open>PO B Par A M\<close> \<open>\<not> Col PO A' B'\<close> assms(6) assms(7) col_trivial_2 col_trivial_3 colx 
              inter_uniqueness_not_par not_col_permutation_3)
        have "PO \<noteq> P" 
          using \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P A N\<close> \<open>\<not> Col PO A B\<close> l6_16_1 
            not_col_permutation_3 by blast
        have "P \<noteq> N" 
          by (metis \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P PO C\<close> \<open>PO N Par A C\<close> 
              \<open>\<not> Col PO A B\<close> col_trivial_2 colx inter_uniqueness_not_par 
              not_col_permutation_4 not_col_permutation_5)
        show ?thesis 
        proof (rule l13_11 [where ?PO="P" and ?C="A" and ?C'="PO"], simp_all add: 
            \<open>B \<noteq> P\<close> \<open>A \<noteq> P\<close> \<open>M \<noteq> P\<close> \<open>PO \<noteq> P\<close>)
          show "\<not> Col P N C" 
            by (metis \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P A N\<close> \<open>P \<noteq> N\<close> assms(1) col3 not_col_distincts)
          show "Col P N B" 
            by (metis \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P A N\<close> col2__eq col_permutation_2)
          thus "Col P B A" 
            using \<open>Col P A N\<close> \<open>P \<noteq> N\<close> col_permutation_5 col_trivial_3 colx by blast
          show "Col P C M" 
            by (metis Col_cases \<open>C \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col P PO C\<close> col2__eq)
          show "Col P M PO" 
            using \<open>C \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col P PO C\<close> col2__eq col_permutation_5 by blast
          show "B PO Par A M" 
            using Par_cases \<open>PO B Par A M\<close> by blast
          show "A C Par N PO" 
            using Par_cases \<open>PO N Par A C\<close> by blast
        qed
      qed
      have "N M Par B' C'" 
      proof (cases "N B' Par PO C'")
        case True
        have "N B' ParStrict PO C'" 
          by (metis Par_cases Par_def True \<open>A' C' Par PO N\<close> \<open>\<not> Col PO A' C'\<close> 
              par_strict_not_col_4)
        have "M \<noteq> L" 
          by (metis \<open>C \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col N L B'\<close> \<open>N B' ParStrict PO C'\<close> 
              assms(8) colx not_col_distincts par_not_col)
        have "L \<noteq> C'" 
          using \<open>Col N L B'\<close> \<open>N B' ParStrict PO C'\<close> col_permutation_5 
            par_strict_not_col_4 by blast
        have "L M Par PO B'" 
        proof (rule par_col_par_2 [where ?B="A"])
          show "L \<noteq> M"
            using \<open>M \<noteq> L\<close> by auto
          show "Col L A M" 
            using Col_cases \<open>Col A X Y\<close> \<open>Col M X Y\<close> \<open>X \<noteq> Y\<close> calculation(1) col3 by blast
          show "L A Par PO B'"
            using Par_cases \<open>A L Par PO B'\<close> by auto
        qed
        have "L C' Par PO N" 
          using par_col_par_2 [where ?B="A'"] \<open>L \<noteq> C'\<close> calculation(2)
            \<open>PO N Par L A'\<close> par_symmetry by meson
        have "N M Par C' B'" 
        proof (rule l13_14 [where ?PO="B'" and ?O'="PO" and ?C="L" and ?C'="PO"])
          show "B' N ParStrict PO C'" 
            using Par_strict_cases \<open>N B' ParStrict PO C'\<close> by blast
          show "Col B' N B'" 
            by (simp add: col_trivial_3)
          show "Col B' B' L" 
            by (simp add: col_trivial_1)
          show "Col B' N L" 
            using Col_cases \<open>Col N L B'\<close> by blast
          show "Col PO C' M" 
            by (metis \<open>C \<noteq> PO\<close> \<open>Col M PO C\<close> assms(8) col_permutation_1 col_trivial_2 colx)
          show "Col PO M PO" 
            by (simp add: col_trivial_3)
          show "Col PO C' PO" 
            by (simp add: col_trivial_3)
          show "N PO Par C' L" 
            using Par_cases \<open>L C' Par PO N\<close> by auto
          show "B' PO Par M L" 
            using Par_cases \<open>L M Par PO B'\<close> by blast
        qed
        thus ?thesis 
          using Par_cases by blast
      next
        case False
        hence "\<not> N B' Par PO C'" 
          by blast
        have "Coplanar N B' PO C'" 
        proof (rule coplanar_pseudo_trans [where ?P="PO" and ?Q="A" and ?R="B"], 
            simp_all add: \<open>\<not> Col PO A B\<close>)
          show "Coplanar PO A B N" 
            using Col_cases \<open>Col N A B\<close> ncop__ncols by blast
          show "Coplanar PO A B B'" 
            using assms(7) ncop__ncols by blast
          show "Coplanar PO A B PO" 
            using ncop_distincts by blast
          show "Coplanar PO A B C'" 
            by (metis \<open>C \<noteq> PO\<close> \<open>Coplanar PO A B PO\<close> assms(3) assms(8) 
                col_cop2__cop coplanar_perm_2)
        qed
        then obtain P where "Col P N B'" and "Col P PO C'" 
          using False cop_npar__inter_exists by blast
        have "B' \<noteq> P" using \<open>\<not> Col PO B C\<close> 
          by (metis \<open>B' \<noteq> PO\<close> \<open>C' \<noteq> PO\<close> \<open>Col P PO C'\<close> assms(7) assms(8) 
              col_transitivity_2 not_col_distincts)
        show ?thesis 
        proof (cases "C' = L")
          case True
          hence "C' = L" 
            by blast
          have "C' = M" 
          proof (cases "Col PO X C")
            case True
            show ?thesis
            proof (rule l6_21 [where ?A="PO" and ?B="C" and ?C="Y" and ?D="X"], 
                simp_all add: assms(8))
              show "\<not> Col PO C Y" 
                by (metis True \<open>C \<noteq> PO\<close> \<open>PO B Par X Y\<close> \<open>\<not> Col PO B C\<close> 
                    col_permutation_5 par_col2_par_bis par_id)
              show "Y \<noteq> X" 
                using \<open>X \<noteq> Y\<close> by auto
              show "Col PO C M" 
                using Col_cases \<open>Col M PO C\<close> by blast
              show "Col Y X C'" 
                using Col_cases \<open>C' = L\<close> calculation(1) by blast
              show "Col Y X M" 
                using Col_cases \<open>Col M X Y\<close> by auto
            qed
          next
            case False
            then show ?thesis 
              using True \<open>Col M PO C\<close> \<open>Col M X Y\<close> \<open>X \<noteq> Y\<close> assms(8) 
                calculation(1) l6_21 not_col_permutation_2 not_col_permutation_3 by blast
          qed
          then show ?thesis 
            by (metis True \<open>A' C' Par PO N\<close> \<open>Col A' B' C' \<Longrightarrow> False\<close> \<open>Col N L B'\<close> 
                \<open>\<not> Col PO A' C'\<close> calculation(2) col_par not_col_permutation_2 
                par_comm par_id_4 par_right_comm)
        next
          case False
          hence "C'\<noteq> L" 
            by blast
          {
            assume "L = P" 
            hence "Col C' PO A'" 
              by (metis Col_cases False \<open>Col P PO C'\<close> calculation(2) col_transitivity_1)
            hence "Col PO A' C'" 
              using Col_cases by blast
            hence False 
              by (simp add: \<open>\<not> Col PO A' C'\<close>)
          }
          show ?thesis 
          proof (cases "L = M")
            case True
            have "C' = M"
            proof (rule l6_21 [where ?A="PO" and ?B="C" and ?C="A'" and ?D="C'"],
                simp_all add: assms(8))
              show "\<not> Col PO C A'" 
                by (metis \<open>C \<noteq> PO\<close> \<open>\<not> Col PO A' C'\<close> assms(8) col_transitivity_1)
              show "A' \<noteq> C'" 
                using \<open>\<not> Col PO C A'\<close> assms(8) by auto
              show "Col PO C M" 
                using Col_cases \<open>Col M PO C\<close> by blast
              show "Col A' C' C'" 
                using not_col_distincts by blast
              show "Col A' C' M" 
                using True calculation(2) not_col_permutation_2 by blast
            qed
            then show ?thesis 
              using False True by auto
          next
            case False
            hence "L \<noteq> M"
              by blast
            have "L M Par PO B'"
            proof (rule par_col_par_2 [where ?B="A"], simp_all add:False)
              show "Col L A M" 
                using Col_cases \<open>Col A X Y\<close> \<open>Col M X Y\<close> \<open>X \<noteq> Y\<close> calculation(1) col3 by blast
              show "L A Par PO B'" 
                using Par_cases \<open>A L Par PO B'\<close> by auto
            qed
            have "L C' Par N PO" 
              by (metis Par_cases \<open>C' \<noteq> L\<close> \<open>PO N Par L A'\<close> calculation(2) par_col_par)
            have "B'\<noteq> N" 
              using \<open>Col N A B\<close> \<open>\<not> Col B' A B\<close> by blast
            show ?thesis 
            proof (rule l13_11 [where ?PO="P" and ?C="L" and ?C'="PO"], simp_all add: \<open>B' \<noteq> P\<close>
                \<open>Col P N B'\<close> \<open>L C' Par N PO\<close>)
              {
                assume "Col P N C'"
                hence "Col P B' C'" 
                  by (metis \<open>Col P N B'\<close> \<open>Col P PO C'\<close> \<open>PO N Par A C\<close> \<open>\<not> Col PO A' C'\<close> 
                      assms(5) calculation(2) col_permutation_3 col_transitivity_1 par_strict_par 
                      par_symmetry parallel_uniqueness)
                have "Col C' PO B'" 
                proof (rule col_transitivity_1 [where ?Q="P"])
                  show "C' \<noteq> P" 
                    by (metis \<open>B' \<noteq> N\<close> \<open>C' \<noteq> L\<close> \<open>Col A' B' C' \<Longrightarrow> False\<close> \<open>Col N L B'\<close> 
                        \<open>Col P N B'\<close> calculation(2) col_transitivity_1 not_col_permutation_1)
                  show "Col C' P PO" 
                    using Col_cases \<open>Col P PO C'\<close> by blast
                  show "Col C' P B'" 
                    using Col_cases \<open>Col P B' C'\<close> by auto
                qed
                hence "Col PO B C'" 
                  by (metis \<open>B' \<noteq> PO\<close> assms(7) col_trivial_2 col_trivial_3 l6_21)
                hence False           
                  by (metis \<open>C \<noteq> PO\<close> \<open>C' \<noteq> PO\<close> \<open>PO B Par X Y\<close>  \<open>X Y Par PO C \<Longrightarrow> False\<close> 
                      assms(8) not_par_not_col par_col_par_2 par_symmetry par_trans)
              }
              thus "\<not> Col P N C'" 
                by blast
              show "L \<noteq> P" 
                using \<open>L = P \<Longrightarrow> False\<close> by blast
              show "Col P B' L" 
                by (metis Col_cases \<open>B' \<noteq> N\<close> \<open>Col N L B'\<close> \<open>Col P N B'\<close> l6_16_1)
              show "M \<noteq> P" 
                by (metis Col_cases Par_def Par_strict_cases \<open>A L ParStrict PO B'\<close> 
                    \<open>Col P B' L\<close> \<open>L M Par PO B'\<close> par_strict_not_col_4)
              show "PO \<noteq> P" 
                using \<open>A L ParStrict PO B'\<close> \<open>Col P B' L\<close> col_permutation_2 
                  par_strict_not_col_2 by blast
              show "Col P C' M" 
                by (metis \<open>C \<noteq> PO\<close> \<open>C' \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col P PO C'\<close> 
                    assms(8) l6_16_1 not_col_permutation_1)
              show "Col P M PO" 
                by (metis \<open>C \<noteq> PO\<close> \<open>C' \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col P PO C'\<close> 
                    assms(8) col_permutation_2 l6_16_1)
              show "B' PO Par L M" 
                using Par_cases \<open>L M Par PO B'\<close> by auto
            qed
          qed
        qed
      qed
      thus ?thesis 
        using Par_cases \<open>N M Par B C\<close> par_trans by blast
    qed
    ultimately show ?thesis
      using cop_npar__inter_exists by blast
  qed
qed

lemma (in Tarski_Euclidean) l13_15_2_aux:
  assumes "\<not> Col A B C" and
    "\<not> PO A Par B C" and
    "PO B Par A C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "Col PO A A'" and
    "Col PO B B'" and
    "Col PO C C'"
  shows "B C Par B' C'" 
proof -
  have "\<not> Col PO A B" 
    by (metis assms(4) assms(6) assms(7) col3 not_col_distincts par_not_col)
  have "\<not> Col PO B C" 
    using \<open>\<not> Col PO A B\<close> assms(3) col_permutation_5 col_trivial_2 not_strict_par by blast
  have "\<not> Col PO A C" 
    using \<open>\<not> Col PO B C\<close> assms(3) col_trivial_3 not_col_permutation_2 not_strict_par2 by blast
  have "PO \<noteq> A" 
    using \<open>\<not> Col PO A B\<close> col_trivial_1 by blast
  have "PO \<noteq> B" 
    using \<open>\<not> Col PO B C\<close> col_trivial_1 by auto
  have "PO \<noteq> C" 
    using \<open>\<not> Col PO B C\<close> not_col_distincts by presburger
  have "PO \<noteq> A'" 
    using assms(5) assms(8) col_permutation_4 par_strict_not_col_2 by blast
  have "PO \<noteq> B'" 
    using assms(4) assms(6) col_permutation_2 par_strict_not_col_3 by blast
  have "PO \<noteq> C'" 
    using assms(5) assms(6) col_permutation_2 par_strict_not_col_3 by blast
  have "\<not> Col PO A' B'" 
    by (meson \<open>PO \<noteq> A'\<close> assms(4) assms(6) col_transitivity_2 not_col_permutation_5 
        par_strict_not_col_3)
  have "\<not> Col PO B' C'" 
    by (metis \<open>PO \<noteq> B'\<close> \<open>PO \<noteq> C'\<close> \<open>\<not> Col PO B C\<close> assms(7) assms(8) col2__eq col_permutation_4)
  have "\<not> Col PO A' C'" 
    by (metis Col_cases \<open>PO \<noteq> A'\<close> assms(5) assms(6) col2__eq par_strict_not_col_3)
  have "A \<noteq> A'" 
    using assms(5) not_par_strict_id by blast  
  have "B \<noteq> B'" 
    using assms(4) col_trivial_2 par_strict_not_col_4 by blast
  have "C \<noteq> C'" 
    using assms(5) col_trivial_2 par_strict_not_col_4 by blast
  show ?thesis
  proof (cases "B C Par B' C'")
    case True
    then show ?thesis 
      by blast
  next
    case False
    hence "B \<noteq> C" 
      using assms(1) not_col_distincts by presburger
    hence "\<exists> C0 D. C0 \<noteq> D \<and> B C Par C0 D \<and> Col B' C0 D" 
      using parallel_existence by auto
    then obtain X Y where "X \<noteq> Y" and "B C Par X Y" and "Col B' X Y"
      by blast
    {
      assume "X Y Par PO C"
      hence "PO C Par B C" 
        using Par_cases \<open>B C Par X Y\<close> not_par_one_not_par by blast
      hence False 
        using \<open>\<not> Col PO B C\<close> par_comm par_id_2 by blast
    }
    have "Coplanar X Y PO C" 
    proof -
      {
        assume "B C ParStrict X Y"
        have "Coplanar X Y PO C" 
        proof (rule coplanar_pseudo_trans [where ?P="B" and ?Q="C" and ?R="B'"])
          show "\<not> Col B C B'" 
            using \<open>B C ParStrict X Y\<close> \<open>Col B' X Y\<close> col_permutation_2 par_not_col by blast
          show "Coplanar B C B' X" 
            using \<open>B C Par X Y\<close> \<open>Col B' X Y\<close> ncop_distincts not_col_distincts 
              par_col2_par_bis par_cong_cop by blast
          show "Coplanar B C B' Y" 
            using ParStrict_def \<open>B C ParStrict X Y\<close> \<open>Col B' X Y\<close> \<open>Coplanar B C B' X\<close> 
              col_cop__cop by blast
          show "Coplanar B C B' PO" 
            using Col_cases assms(7) ncop__ncols by blast
          show "Coplanar B C B' C" 
            using ncop_distincts by blast
        qed
      }
      moreover have "B \<noteq> C \<and> X \<noteq> Y \<and> Col B X Y \<and> Col C X Y \<longrightarrow> Coplanar X Y PO C" 
        using col_permutation_1 ncop__ncols by blast
      ultimately show ?thesis
        using Par_def \<open>B C Par X Y\<close> by force
    qed
    obtain C'' where "Col C'' X Y" and "Col C'' PO C" 
      using \<open>Coplanar X Y PO C\<close> \<open>X Y Par PO C \<Longrightarrow> False\<close> cop_npar__inter_exists by blast
    hence "B' \<noteq> C''" 
      using \<open>PO \<noteq> C\<close> \<open>\<not> Col PO B' C'\<close> assms(8) col_permutation_4 col_trivial_2 colx by blast
    have "B' C'' Par B C" 
      by (metis \<open>B C Par X Y\<close> \<open>B' \<noteq> C''\<close> \<open>Col B' X Y\<close> \<open>Col C'' X Y\<close> \<open>X \<noteq> Y\<close> 
          col2__eq col_par not_par_one_not_par par_col_par_2 par_left_comm)
    have "A C Par A' C''" 
    proof (rule l13_15_1 [where ?PO="PO" and ?A="B" and ?A'="B'"], 
        simp_all add: assms(2) assms(6) assms(7))
      show "\<not> Col B A C" 
        using Col_cases assms(1) by auto
      show "Coplanar PO A B C" 
        using assms(3) coplanar_perm_2 par_cong_cop by blast
      show "B A ParStrict B' A'" 
        using Par_strict_cases assms(4) by blast
      show "B C ParStrict B' C''" 
        by (metis Col_cases Par_def Par_strict_cases \<open>B \<noteq> B'\<close> \<open>B' C'' Par B C\<close> 
            \<open>\<not> Col PO B C\<close> assms(7) l6_16_1)
      show "Col PO C C''" 
        using Col_cases \<open>Col C'' PO C\<close> by blast
    qed
    have "C' \<noteq> C''" 
      using False \<open>B' C'' Par B C\<close> par_symmetry by blast
    have "A' C' Par A' C''" 
      using \<open>A C Par A' C''\<close> assms(5) par_strict_par par_symmetry 
        postulate_of_transitivity_of_parallelism_def 
        postulate_of_transitivity_of_parallelism_thm by blast
    hence "C' = C''" 
      by (metis \<open>Col C'' PO C\<close> \<open>PO \<noteq> C\<close> assms(5) assms(8) col_transitivity_2 
          not_col_permutation_2 par_id_4 par_strict_not_col_2)
    thus ?thesis 
      by (simp add: \<open>C' \<noteq> C''\<close>)
  qed
qed

lemma (in Tarski_Euclidean) l13_15_2:
  assumes "\<not> Col A B C" and
    "PO B Par A C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "Col PO A A'" and
    "Col PO B B'" and
    "Col PO C C'"
  shows "B C Par B' C'" 
proof (cases "B C Par B' C'")
  case True
  then show ?thesis 
    by blast
next
  case False
  have "\<not> B C Par PO A \<or> \<not> B' C' Par PO A" 
    using False not_par_one_not_par by blast
  moreover {
    assume "\<not> B C Par PO A" 
    hence "\<not> PO A Par B C" 
      using Par_cases by blast
    hence False 
      using False assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) 
        l13_15_2_aux by blast
  }
  moreover {
    assume "\<not> B' C' Par PO A" 
    have "\<not> Col A' B' C'" 
      by (metis assms(1) assms(3) assms(4) par_id par_strict_col_par_strict 
          par_strict_neq2 par_strict_symmetry par_strict_trans)
    moreover have "B' \<noteq> PO" 
      using assms(3) assms(5) col_permutation_2 par_strict_not_col_3 by blast
    have "PO B Par PO B'" 
      by (metis \<open>B' \<noteq> PO\<close> assms(2) assms(6) not_par_not_col par_distinct)
    have "\<not> PO A' Par B' C'" 
      by (metis \<open>\<not> B C Par PO A \<Longrightarrow> False\<close> \<open>\<not> B' C' Par PO A\<close> assms(5)
          not_par_not_col not_par_one_not_par par_distinct par_symmetry)
    moreover have "PO B' Par A' C'" 
      by (metis Par_def Par_perm \<open>PO B Par PO B'\<close> assms(2) assms(4) par_trans)
    ultimately have "B' C' Par B C" 
      using l13_15_2_aux assms(3) assms(4) assms(5) assms(6) assms(7) 
        col_permutation_5 par_strict_symmetry by blast 
    hence False 
      using False Par_cases by auto
  }
  ultimately show ?thesis 
    by blast
qed

lemma (in Tarski_Euclidean) l13_15:
  assumes "\<not> Col A B C" and
    "Coplanar PO B A C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "Col PO A A'" and
    "Col PO B B'" and
    "Col PO C C'"
  shows "B C Par B' C'" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) l13_15_1 l13_15_2 by blast

lemma (in Tarski_Euclidean) l13_15_par: 
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "A A' Par B B'" and
    "A A' Par C C'" 
  shows "B C Par B' C'" 
proof -
  have "Plg B' A' A B" 
    by (meson Par_cases Par_strict_cases assms(2) assms(4) pars_par_plg)
  hence "Parallelogram B' A' A B" 
    using parallelogram_equiv_plg by force
  hence "Parallelogram A' A B B'"
    using Plg_perm by blast 
  hence "Parallelogram B B' A' A" 
    using plg_sym by blast
  moreover have "Plg A' C' C A" 
    using Par_cases Par_strict_cases assms(3) assms(5) pars_par_plg by blast
  hence "Parallelogram A' C' C A" 
    using parallelogram_equiv_plg by force
  hence "Parallelogram C' C A A'"
    using Plg_perm by blast
  hence "Parallelogram A' A C C'" 
    using plg_comm2 plg_sym by blast
  ultimately have "Parallelogram B B' C' C \<or> (B = B' \<and> A' = A \<and> C' = C \<and> B = C)" 
    using plg_pseudo_trans by blast
  have "B B' Par C C'" 
    using assms(4) assms(5) not_par_one_not_par par_symmetry by blast
  moreover {
    assume "B B' ParStrict C C'"
    hence "B C Par B' C'" 
      using \<open>Parallelogram B B' C' C \<or> B = B' \<and> A' = A \<and> C' = C \<and> B = C\<close> 
        ncol124_plg__pars1423 par_strict_not_col_1 par_strict_par by blast
  }
  ultimately show ?thesis 
    by (metis Col_def \<open>Parallelogram B B' C' C \<or> B = B' \<and> A' = A \<and> C' = C \<and> B = C\<close> 
        assms(1) between_trivial par_neq1 plg_par_2 plg_trivial plg_uniqueness)
qed

lemma (in Tarski_Euclidean) l13_18_2: 
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "B C ParStrict B' C'" and
    "Col PO A A'" and
    "Col PO B B'" 
  shows "Col PO C C'" 
proof -
  have "\<not> Col PO A B" 
    by (metis assms(2) assms(5) assms(6) col_transitivity_2 par_strict_not_col_1 
        par_strict_not_col_4)
  have "Coplanar B' C' PO C" 
    by (metis NCol_cases assms(4) assms(6) coplanar_trans_1 ncop__ncols 
        ncoplanar_perm_4 par_strict_left_comm par_strict_not_col_2 pars__coplanar)
  moreover have "\<not> B' C' Par PO C" 
    by (metis Par_perm Par_strict_perm assms(2) assms(4) assms(5) assms(6) 
        col_transitivity_2 not_par_one_not_par par_id_2 par_strict_not_col_3 par_strict_par)
  ultimately have "\<exists> X. Col X B' C' \<and> Col X PO C" 
    using cop_npar__inter_exists by blast
  then obtain C'' where "Col C'' B' C'" and "Col C'' PO C" 
    by blast
  show ?thesis
  proof (cases "Col PO C C'")
    case True
    then show ?thesis 
      by simp
  next
    case False
    hence "C' C'' Par B C" 
      by (metis NCol_perm Par_def Par_strict_perm \<open>Col C'' B' C'\<close> \<open>Col C'' PO C\<close> 
          assms(4) par_col_par_2)
    have "C' C'' ParStrict B C" 
      using Par_def \<open>C' C'' Par B C\<close> \<open>Col C'' B' C'\<close> assms(4) par_not_col by blast
    have "\<not> Col PO B C" 
      by (metis \<open>\<not> Col PO A B\<close> assms(4) assms(6) col_transitivity_2 col_trivial_3 
          par_strict_not_col_1)
    have "B' C'' Par B C" 
      by (metis Par_cases \<open>C' C'' Par B C\<close> \<open>Col C'' B' C'\<close> \<open>Col C'' PO C\<close> 
          \<open>\<not> Col PO B C\<close> assms(2) assms(4) assms(5) assms(6) col_par l6_16_1 
          not_col_permutation_1 not_par_one_not_par par_strict_not_col_3 par_strict_par)
    have "B' C'' ParStrict B C" 
      using Par_def \<open>B' C'' Par B C\<close> \<open>C' C'' ParStrict B C\<close> par_strict_not_col_2 by blast
    have "A C Par A' C''" 
    proof (rule l13_15 [where ?A="B" and ?PO="PO" and ?A'="B'"],simp_all add:assms(6) assms(5))
      show "\<not> Col B A C" 
        using Col_cases assms(1) by blast
      show "Coplanar PO A B C" 
      proof -
        have "\<not> Col PO A' B'" 
          by (metis Col_cases assms(2) assms(5) assms(6) colx not_col_distincts 
              par_strict_not_col_2 par_strict_not_col_3)
        moreover have "Coplanar PO A' B' PO" 
          using ncop_distincts by blast
        moreover have "Coplanar PO A' B' A" 
          using Col_cases assms(5) ncop__ncols by blast
        moreover have "Coplanar PO A' B' B" 
          using Col_cases assms(6) ncop__ncols by blast
        moreover have "Coplanar PO A' B' C" 
        proof -
          have "\<not> Col PO A C'" 
            by (metis \<open>\<not> Col PO A B\<close> assms(3) assms(5) col_transitivity_2 col_trivial_1 
                not_col_permutation_2 par_strict_not_col_3)
          moreover have "Coplanar PO A C' PO" 
            using ncop_distincts by blast
          moreover have "Coplanar PO A C' A'" 
            using assms(5) ncop__ncols by blast
          moreover have "Coplanar PO A C' B'" 
            by (smt (verit) Col_def False \<open>Coplanar B' C' PO C\<close> assms(3) calculation(3) 
                coplanar_perm_21 coplanar_perm_8 coplanar_trans_1 
                par_strict_not_col_3 pars__coplanar)
          moreover have "Coplanar PO A C' C" 
            by (metis \<open>Coplanar B' C' PO C\<close> \<open>\<not> Col PO A' B'\<close> assms(4) assms(6) 
                calculation(4) col_transitivity_2 coplanar_perm_22 
                coplanar_perm_8 coplanar_trans_1 not_col_distincts par_strict_not_col_3)
          ultimately show ?thesis 
            using coplanar_pseudo_trans by blast
        qed
        ultimately show ?thesis 
          using coplanar_pseudo_trans by blast
      qed
      show "B A ParStrict B' A'" 
        using Par_strict_cases assms(2) by auto
      show "B C ParStrict B' C''" 
        using Par_strict_cases \<open>B' C'' ParStrict B C\<close> by blast
      show "Col PO C C''" 
        using Col_cases \<open>Col C'' PO C\<close> by blast
    qed
    hence "A' C' Par A' C''" 
      using assms(3) par_strict_par par_symmetry 
        postulate_of_transitivity_of_parallelism_def 
        postulate_of_transitivity_of_parallelism_thm by blast
    hence "\<not> Col A' B' C'" 
      by (metis \<open>A C Par A' C''\<close> assms(1) assms(2) col2__eq not_par_one_not_par 
          par_col2_par_bis par_id par_strict_neq2 par_strict_par)
    hence "C = C''" 
      by (metis False \<open>A' C' Par A' C''\<close> \<open>Col C'' B' C'\<close> \<open>Col C'' PO C\<close> 
          col2__eq col_permutation_4 col_permutation_5 par_id)
    then show ?thesis 
      using \<open>Col C'' B' C'\<close> assms(4) par_strict_not_col_2 by blast
  qed
qed

lemma (in Tarski_Euclidean) l13_18_3_R1: 
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "B C ParStrict B' C'" and
    "A A' Par B B'"
  shows "C C' Par A A'" 
proof -
  have "A \<noteq> A'" 
    using assms(5) par_neq1 by auto
  have "B \<noteq> B'" 
    using assms(4) not_par_strict_id by blast
  then obtain P where "B B' Par C P" 
    using parallel_existence1 by blast
  show ?thesis
  proof (cases "C P Par B C")
    case True
    {
      assume "C P ParStrict B C"
      hence ?thesis 
        using Par_strict_cases not_par_strict_id by blast
    }
    then show ?thesis 
      by (metis Par_def Par_perm True \<open>B B' Par C P\<close> assms(4) col_trivial_1 
          par_not_col par_strict_not_col_3)
  next
    case False
    have "\<not> C P Par B' C'" 
      using False assms(4) not_par_one_not_par par_strict_par by blast
    have "\<not> Col B C B'" 
      using assms(4) par_strict_not_col_1 by auto
    have "Coplanar C P B' C'" 
    proof -
      have "\<not> Col B C B'" 
        using assms(4) par_strict_not_col_1 by auto
      moreover have "Coplanar B C B' B" 
        using ncop_distincts by blast
      moreover have "Coplanar B C B' C" 
        using ncop_distincts by auto
      moreover have "Coplanar B C B' B'" 
        using ncop_distincts by blast
      moreover have "Coplanar B C B' C'"
        using assms(4) pars__coplanar by blast
      ultimately show ?thesis 
        by (metis \<open>B B' Par C P\<close> coplanar_perm_2 coplanar_trans_1 par_cong_cop)
    qed
    then obtain C'' where "Col C'' C P" and "Col C'' B' C'" 
      using \<open>\<not> C P Par B' C'\<close> cop_npar__inter_exists by blast
    show ?thesis 
    proof (cases "B' = C''")
      case True
      then show ?thesis 
        by (metis \<open>B B' Par C P\<close> \<open>Col C'' C P\<close> \<open>\<not> Col B C B'\<close> 
            col_par not_col_distincts not_par_one_not_par par_distinct par_id_2)
    next
      case False
      have "C C'' Par B B'" 
        by (metis \<open>B B' Par C P\<close> \<open>Col C'' B' C'\<close> \<open>Col C'' C P\<close> assms(4) 
            col_permutation_4 not_par_not_col not_par_one_not_par
            par_distinct par_strict_not_col_2)
      have "B' C'' Par B C" 
        by (metis False \<open>Col C'' B' C'\<close> assms(4) col_par not_par_one_not_par 
            par_left_comm par_strict_neq2 par_strict_par)
      {
        assume "Col A' B' C'" 
        hence "C' A' Par B C" 
          by (metis Par_cases assms(3) assms(4) col_transitivity_1 not_col_permutation_5 
              par_col2_par_bis par_strict_neq2 par_strict_par)
        hence "B C Par A C" 
          using Par_cases assms(3) not_par_one_not_par par_strict_par by blast
        {
          assume "B C ParStrict A C"
          hence "Col A B C" 
            using col_trivial_2 par_strict_not_col_4 by blast
        }
        hence "Col A B C" 
          using Par_cases \<open>B C Par A C\<close> par_id_2 by blast
        hence False 
          by (simp add: assms(1))
      }
      have "A C Par A' C''" 
      proof (rule l13_15_par [where ?A="B" and ?A'="B'"])
        show "\<not> Col B A C" 
          using Col_cases assms(1) by blast
        show "B A ParStrict B' A'" 
          using Par_strict_cases assms(2) by blast
        show "B C ParStrict B' C''" 
          using Par_def \<open>B' C'' Par B C\<close> \<open>\<not> Col B C B'\<close> not_col_permutation_2 
            par_strict_symmetry by blast
        show "B B' Par A A'" 
          using Par_cases assms(5) by auto
        show "B B' Par C C''" 
          using Par_cases \<open>C C'' Par B B'\<close> by blast
      qed
      have "C' = C''" 
      proof (rule l6_21 [where ?A="C'" and ?B="A'" and ?C="B'" and ?D="C'"])
        show "\<not> Col C' A' B'" 
          using Col_cases \<open>Col A' B' C' \<Longrightarrow> False\<close> by blast
        show "B' \<noteq> C'" 
          using \<open>Col A' B' C' \<Longrightarrow> False\<close> col_trivial_2 by auto
        show "Col C' A' C'" 
          by (simp add: col_trivial_3)
        show "Col C' A' C''" 
          by (meson Par_def \<open>A C Par A' C''\<close> assms(3) col_trivial_1 parallel_uniqueness)
        show "Col B' C' C'" 
          by (simp add: col_trivial_2)
        show "Col B' C' C''" 
          using Col_cases \<open>Col C'' B' C'\<close> by auto
      qed
      thus ?thesis 
        using \<open>C C'' Par B B'\<close> assms(5) not_par_one_not_par by blast
    qed
  qed
qed

lemma (in Tarski_Euclidean) l13_18_3_R2: 
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "B C ParStrict B' C'" and
    "A A' Par B B'"
  shows "C C' Par B B'" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) l13_18_3_R1 par_trans by blast

lemma (in Tarski_Euclidean) l13_18_3:
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "B C ParStrict B' C'" and
    "A A' Par B B'"
  shows "C C' Par A A' \<and> C C' Par B B'" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) l13_18_3_R1 l13_18_3_R2 by blast

lemma (in Tarski_Euclidean) l13_18:  
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" 
  shows "(B C ParStrict B' C' \<and> Col PO A A' \<and> Col PO B B' \<longrightarrow> Col PO C C')
\<and> ((B C ParStrict B' C' \<and> A A' Par B B') \<longrightarrow> (C C' Par A A' \<and> C C' Par B B'))
\<and> (A A' Par B B' \<and> A A' Par C C' \<longrightarrow> B C Par B' C')" 
  by (meson assms(1) assms(2) assms(3) l13_15_par l13_18_2 l13_18_3_R1 l13_18_3_R2)

lemma (in Tarski_Euclidean) l13_19_aux: 
  assumes "\<not> Col PO A B" and
    "A \<noteq> A'" and
    "A \<noteq> C" and
    "PO \<noteq> A" and
    "PO \<noteq> A'" and
    "PO \<noteq> C" and
    "PO \<noteq> C'" and
    "PO \<noteq> B" and 
    "PO \<noteq> B'" and
    "PO \<noteq> D" and
    "PO \<noteq> D'" and
    "Col PO A C" and
    "Col PO A A'" and
    "Col PO A C'" and
    "Col PO B D" and
    "Col PO B B'" and
    "Col PO B D'" and
    "\<not> A B Par C D" and
    "A B Par A' B'" and
    "A D Par A' D'" and
    "B C Par B' C'" 
  shows "C D Par C' D'" 
proof -
  have "Coplanar A B C D" 
    using Col_cases Coplanar_def assms(12) assms(15) by auto
  then obtain E where "Col E A B" and "Col E C D" 
    using \<open>Coplanar A B C D\<close> assms(18) cop_npar__inter_exists by blast
  hence "\<not> A' B' Par PO E" 
    by (meson assms(1) assms(19) col_trivial_3 par_symmetry parallel_uniqueness)
  have "Coplanar A' B' PO E" 
  proof (rule coplanar_pseudo_trans [where ?P="PO" and ?Q="A" and ?R="B"], simp_all add:assms(1))
    show "Coplanar PO A B A'" 
      using assms(13) ncop__ncols by blast
    show "Coplanar PO A B B'" 
      using assms(16) ncop__ncols by blast
    show "Coplanar PO A B PO" 
      using ncop_distincts by blast
    show "Coplanar PO A B E" 
      using \<open>Col E A B\<close> ncop__ncols not_col_permutation_2 by blast
  qed
  then obtain E' where "Col E' A' B'" and "Col E' PO E" 
    using \<open>\<not> A' B' Par PO E\<close> cop_npar__inter_exists by blast
  have "C \<noteq> E" 
    using \<open>Col E A B\<close> assms(1) assms(12) assms(3) l6_16_1 not_col_permutation_3 by blast
  show ?thesis
  proof (cases "Col A D E")
    case True
    hence "B = D" 
      by (metis \<open>C \<noteq> E\<close> \<open>Col E A B\<close> \<open>Col E C D\<close> assms(1) assms(10) assms(12) assms(15) 
          col2__eq col_permutation_2)
    hence "A' B' Par A' D'" 
      using assms(19) assms(20) par_symmetry par_trans by blast
    moreover {
      assume "A' B' ParStrict A' D'"
      hence ?thesis 
        by (simp add: not_par_strict_id)
    }
    ultimately show ?thesis 
      by (metis NCol_perm Par_def \<open>B = D\<close> assms(1) assms(13) assms(16) 
          assms(17) assms(21) assms(5) col_trivial_3 colx par_comm)
  next
    case False
    have "B \<noteq> B'" 
      using Par_perm assms(1) assms(13) assms(19) assms(2) l6_16_1 par_id_3 by blast
    have "D E Par D' E'" 
    proof (rule l13_15 [where ?A="A" and ?PO="PO" and ?A'="A'"], simp_all add: False assms(13))
      show "Coplanar PO D A E" 
        using Coplanar_def NCol_cases \<open>Col E A B\<close> assms(15) by blast
      show "A D ParStrict A' D'" 
        by (metis NCol_cases Par_def assms(1) assms(11) assms(13) assms(17) assms(2) 
            assms(20) col_trivial_3 colx)
      show "A E ParStrict A' E'" 
      proof -
        have "A E Par A' E'" 
          by (metis False NCol_perm \<open>C \<noteq> E\<close> \<open>Col E A B\<close> \<open>Col E C D\<close> \<open>Col E' A' B'\<close> 
              \<open>Col E' PO E\<close> assms(12) assms(13) assms(19) assms(4) assms(5) 
              col_transitivity_1 par_col_par par_col_par_2)
        thus ?thesis 
          by (metis NCol_cases Par_def \<open>Col E' A' B'\<close> assms(1) assms(13) 
              assms(16) assms(2) assms(9) col_transitivity_2)
      qed
      show "Col PO D D'" 
        using assms(15) assms(17) assms(8) col_transitivity_1 by blast
      show "Col PO E E'" 
        using Col_cases \<open>Col E' PO E\<close> by auto
    qed
    have "D C Par D' C'" 
    proof (cases "Col B C E")
      case True
      hence "B = D" 
        by (metis \<open>C \<noteq> E\<close> \<open>Col E C D\<close> assms(1) assms(12) assms(15) assms(6) 
            col2__eq col_permutation_4 col_permutation_5)
      thus ?thesis 
        using False \<open>Col E A B\<close> not_col_permutation_2 by blast
    next
      case False
      have "C E Par C' E'" 
      proof (rule l13_15 [where ?A="B" and ?PO="PO" and ?A'="B'"], simp_all add: False assms(16))
        show "Coplanar PO C B E" 
          using Coplanar_def NCol_perm \<open>Col E A B\<close> assms(12) by blast
        show "B C ParStrict B' C'" 
          by (metis NCol_cases \<open>B \<noteq> B'\<close> assms(1) assms(12) assms(16) assms(21) assms(6) 
              col_trivial_3 colx par_not_col_strict)
        show "B E ParStrict B' E'" 
        proof -
          have "B E Par B' E'" 
          proof (rule par_col_par_2 [where ?B="A"]) 
            show "B \<noteq> E" 
              using False col_trivial_3 by blast
            show "Col B A E" 
              using Col_cases \<open>Col E A B\<close> by blast
            have "B' E' Par B A" 
            proof (rule par_col_par_2 [where ?B="A'"])
              show "B' \<noteq> E'" 
                by (metis \<open>B \<noteq> E\<close> \<open>Col E A B\<close> \<open>Col E' PO E\<close> assms(1) assms(16) 
                    assms(9) col2__eq col_permutation_2)
              show "Col B' A' E'" 
                using Col_cases \<open>Col E' A' B'\<close> by auto
              show "B' A' Par B A" 
                using Par_cases assms(19) by blast
            qed
            thus "B A Par B' E'" 
              using Par_cases by blast
          qed
          thus ?thesis 
            by (metis Par_def \<open>B \<noteq> B'\<close> \<open>Col E A B\<close> assms(1) assms(16) l6_16_1 
                not_col_permutation_2)
        qed
        show "Col PO C C'" 
          using assms(12) assms(14) assms(4) col_transitivity_1 by blast
        show "Col PO E E'" 
          using Col_cases \<open>Col E' PO E\<close> by auto
      qed
      show ?thesis 
      proof (rule par_col_par_2 [where ?B = "E"])
        show "D \<noteq> C" 
          by (metis assms(1) assms(12) assms(15) assms(6) col_trivial_2 colx not_col_permutation_2)
        show "Col D E C" 
          using Col_cases \<open>Col E C D\<close> by auto
        have "D' C' Par D E" 
        proof (rule par_col_par_2 [where ?B = "E'"])
          show "D' \<noteq> C'" 
            using assms(1) assms(14) assms(17) assms(7) col2__eq col_permutation_4 by blast
          show "Col D' E' C'" 
            using Par_perm \<open>C E Par C' E'\<close> \<open>Col D E C\<close> \<open>D E Par D' E'\<close> col_par_par_col by blast
          show "D' E' Par D E" 
            using Par_cases \<open>D E Par D' E'\<close> by blast
        qed
        thus "D E Par D' C'" 
          using Par_cases by blast 
      qed
    qed
    thus ?thesis 
      using Par_cases by blast
  qed
qed

lemma (in Tarski_Euclidean) l13_19:
  assumes "\<not> Col PO A B" and
    "PO \<noteq> A" and
    "PO \<noteq> A'" and
    "PO \<noteq> C" and
    "PO \<noteq> C'" and
    "PO \<noteq> B" and
    "PO \<noteq> B'" and
    "PO \<noteq> D" and
    "PO \<noteq> D'" and
    "Col PO A C" and
    "Col PO A A'" and
    "Col PO A C'" and
    "Col PO B D" and
    "Col PO B B'" and
    "Col PO B D'" and
    "A B Par A' B'" and
    "A D Par A' D'" and
    "B C Par B' C'" 
  shows "C D Par C' D'" 
proof (cases "A = A'")
  case True
  hence "B = B'" 
    using assms(1) assms(14) assms(16) col2__eq col_permutation_5 par_id by blast
  have "D = D'" 
    by (metis True assms(1) assms(13) assms(15) assms(17) colx not_col_permutation_2 
        not_col_permutation_4 par_id_4)
  have "C = C'" 
    using \<open>B = B'\<close> assms(1) assms(10) assms(12) assms(18) colx par_id_2 by blast
  then show ?thesis 
    by (metis NCol_cases \<open>D = D'\<close> assms(1) assms(10) assms(13) assms(4) 
        col_transitivity_2 par_reflexivity)
next
  case False
  hence "A \<noteq> A'"
    by blast
  show ?thesis 
  proof (cases "A = C")
    case True
    have "A' = C'" 
      by (metis True assms(1) assms(11) assms(12) assms(14) assms(16) 
          assms(18) assms(7) col_par_par_col col_trivial_3 colx not_col_permutation_1)
    thus ?thesis 
      using True assms(17) by auto
  next
    case False
    hence "A \<noteq> C" 
      by blast
    then show ?thesis 
    proof (cases "A' = C'")
      case True
      have "A = C" 
        by (metis True assms(1) assms(10) assms(16) assms(18) l6_16_1 
            not_par_one_not_par par_comm par_id)
      thus ?thesis 
        using False by blast
    next
      case False
      hence "A' \<noteq> C'" 
        by blast
      show ?thesis 
      proof (cases "C D Par C' D'")
        case True
        thus ?thesis 
          by simp
      next
        case False
        hence "\<not> C D Par C' D'"
          by blast
        have "\<not> C D Par A' B' \<or> \<not> C' D' Par A' B'" 
          using False not_par_one_not_par by blast
        moreover {
          assume "\<not> C D Par A' B'" 
          hence "\<not> C D Par A B" 
            using assms(16) par_trans by blast
          hence "\<not> A B Par C D" 
            using Par_cases by blast
          hence ?thesis 
            using l13_19_aux 
            using \<open>A \<noteq> A'\<close> \<open>A \<noteq> C\<close> assms(1) assms(10) assms(11) assms(12) assms(13) 
              assms(14) assms(15) assms(16) assms(17) assms(18) assms(2) assms(3) assms(4) 
              assms(5) assms(6) assms(7) assms(8) assms(9) by force
        }
        moreover {
          assume "\<not> C' D' Par A' B'" 
          hence "C' D' Par C D" 
          proof -
            have "\<not> Col PO A' B'" 
              by (meson assms(1) assms(11) assms(14) assms(3) assms(7) col2__eq col_permutation_4)
            moreover have "A' \<noteq> A" 
              using \<open>A \<noteq> A'\<close> by auto
            moreover have "A' \<noteq> C'" 
              using \<open>A' \<noteq> C'\<close> by auto
            moreover have "Col PO A' C'" 
              using assms(11) assms(12) assms(2) col_transitivity_1 by blast
            moreover have "Col PO A' A" 
              using Col_cases assms(11) by auto
            moreover have "Col PO A' C" 
              using assms(10) assms(11) assms(2) col_transitivity_1 by blast
            moreover have "Col PO B' D'" 
              using assms(14) assms(15) assms(6) col_transitivity_1 by blast
            moreover have "Col PO B' B" 
              using Col_cases assms(14) by blast
            moreover have "Col PO B' D" 
              using assms(13) assms(14) assms(6) col_transitivity_1 by blast
            moreover have "\<not> A' B' Par C' D'" 
              using Par_cases \<open>\<not> C' D' Par A' B'\<close> by blast
            moreover have "A' B' Par A B" 
              using Par_cases assms(16) by blast
            moreover have "A' D' Par A D" 
              using Par_cases assms(17) by blast
            moreover have "B' C' Par B C" 
              using Par_cases assms(18) by auto
            ultimately show ?thesis
              using l13_19_aux assms(2) assms(3) assms(4) assms(5) assms(6) assms(7)
                assms(8)assms(9) by force
          qed
          hence ?thesis 
            using Par_cases by blast
        }
        ultimately show ?thesis 
          by blast
      qed
    qed
  qed
qed

lemma (in Tarski_Euclidean) l13_19_par_aux:
  assumes "X \<noteq> A" and
    (*   "X \<noteq> A'" and
    "X \<noteq> C" and
    "X \<noteq> C'" and*)
    "Y \<noteq> B" and
    (*   "Y \<noteq> B'" and
    "Y \<noteq> D" and
    "Y \<noteq> D'" and*)
    "Col X A C" and
    "Col X A A'" and
    "Col X A C'" and
    "Col Y B D" and
    "Col Y B B'" and
    "Col Y B D'" and
    "A \<noteq> C" and
    "B \<noteq> D" and
    "A \<noteq> A'" and
    "X A ParStrict Y B" and
    "\<not> A B Par C D" and
    "A B Par A' B'" and
    "A D Par A' D'" and
    "B C Par B' C'" 
  shows "C D Par C' D'" 
proof -
  have "Coplanar B Y A X" 
    using assms(12) coplanar_perm_23 pars__coplanar by blast
  hence "Coplanar A C B Y" 
    by (meson assms(1) assms(3) col_cop2__cop coplanar_perm_16 ncop_distincts)
  hence "Coplanar A B C D" 
    by (metis assms(6) assms(2) col2_cop2__eq col_trivial_2 coplanar_perm_2 
        ncop_distincts not_col_permutation_3)
  then obtain E where "Col E A B" and "Col E C D" 
    using assms(13) cop_npar__inter_exists by blast
  obtain Z where "X A Par E Z" 
    using assms(1) parallel_existence1 by blast
  hence "\<not> A B Par E Z" 
    using assms(12) not_par_one_not_par par_id_1 par_left_comm par_strict_not_col_4 by blast
  hence "\<not> A' B' Par E Z" 
    using assms(14) postulate_of_transitivity_of_parallelism_def 
      postulate_of_transitivity_of_parallelism_thm by blast
  have "Coplanar A' B' E Z" 
  proof -
    {
      assume "X A ParStrict E Z"
      hence "Coplanar X A E Z" 
        using \<open>X A Par E Z\<close> par_cong_cop by auto
      have "Coplanar X A E A'" 
        using assms(4) ncop__ncols by blast
      have "Coplanar X A E E" 
        using ncop_distincts by blast 
      have "Coplanar X A E B'" 
      proof (cases "Col A B A'")
        case True
        thus ?thesis 
          by (metis \<open>Col E A B\<close> assms(4) assms(11) assms(14) l6_16_1 ncop__ncol 
              not_col_permutation_2 par_distincts)
      next
        case False
        moreover have "Coplanar A B A' B'" 
          by (simp add: assms(14) par_cong_cop)
        moreover have "Coplanar A B A' X" 
          using assms(4) ncop__ncols not_col_permutation_2 by blast
        moreover have "Coplanar A B A' E" 
          using \<open>Col E A B\<close> ncop__ncols not_col_permutation_2 by blast  
        moreover have "Coplanar A B A' A" 
          using ncop_distincts by blast
        ultimately show ?thesis 
          using coplanar_pseudo_trans by presburger
      qed
      have "\<not> Col X A E" 
        using \<open>X A ParStrict E Z\<close> par_strict_not_col_1 by auto
      hence ?thesis 
        by (simp add: \<open>Coplanar X A E A'\<close> \<open>Coplanar X A E B'\<close> \<open>Coplanar X A E E\<close> 
            \<open>Coplanar X A E Z\<close> coplanar_pseudo_trans)
    }
    thus ?thesis 
      by (metis NCol_perm Par_def \<open>X A Par E Z\<close> assms(4) colx ncop__ncols)
  qed
  then obtain E' where "Col E' A' B'" and "Col E' E Z" 
    using \<open>\<not> A' B' Par E Z\<close> cop_npar__inter_exists by blast
  {
    assume "Col A D E" 
    have False
    proof (cases "A = E")
      case True
      then show ?thesis 
        by (metis \<open>Col E C D\<close> assms(1) assms(6) assms(9) assms(12) assms(3) 
            col_par not_col_permutation_1 par_strict_not_col_2 par_strict_par 
            parallel_uniqueness)
    next
      case False
      have "Col A B D" 
        using Col_cases False \<open>Col A D E\<close> \<open>Col E A B\<close> col_transitivity_1 by blast
      have "Col A X A \<and> Col A Y B" 
        by (meson \<open>Col A B D\<close> assms(6) assms(10) assms(12) col2__eq one_side_not_col124 pars__os3412)
      thus ?thesis 
        using assms(12) par_strict_not_col_2 by blast
    qed
  }
  have "X A ParStrict E Z" 
    by (metis \<open>X A Par E Z\<close> Col_def Par_def \<open>Col A D E \<Longrightarrow> False\<close> \<open>Col E A B\<close> assms(12) 
        between_trivial l6_16_1 par_strict_not_col_4)
  have "Y B Par E Z" 
    by (metis Par_perm \<open>X A Par E Z\<close> assms(12) not_par_one_not_par par_strict_par)
  have "Y B ParStrict E Z" 
  proof -
    {
      assume "Y \<noteq> B" and "E \<noteq> Z" and "Col Y E Z" and "Col B E Z"
      have "Col E Y B" 
        by (metis \<open>Col B E Z\<close> \<open>Col Y E Z\<close> \<open>Y B Par E Z\<close> assms(8) col2__eq 
            col_permutation_2 not_strict_par)
      have "Col B D E" 
        using \<open>Col Y E Z\<close> \<open>Y B Par E Z\<close> assms(6) assms(10) assms(2) col_par 
          col_permutation_1 parallel_uniqueness by blast
      have "B = D" 
      proof (rule l6_21 [where ?A="B" and ?B="E" and ?C="C" and ?D="D"])
        {
          assume "Col B E C"
          hence "Col C X A \<and> Col C Y B" 
            by (metis \<open>Col E A B\<close> \<open>Col E C D\<close> assms(6) assms(9) assms(10) 
                assms(12) assms(3) col_permutation_4 col_permutation_5 
                col_trivial_3 colx par_not_col)
          hence False 
            using assms(12) par_not_col by blast
        }
        thus "\<not> Col B E C" 
          by blast
        show "C \<noteq> D" 
          using Col_cases \<open>Col B D E\<close> \<open>\<not> Col B E C\<close> by blast
        show "Col B E B" 
          using not_col_distincts by auto
        show "Col B E D" 
          using Col_cases \<open>Col B D E\<close> by blast
        show "Col C D B" 
          by (metis \<open>Col A D E \<Longrightarrow> False\<close> \<open>Col B D E\<close> \<open>Col E C D\<close> col_permutation_1 
              col_trivial_2 colx)
        show "Col C D D" 
          using col_trivial_2 by auto
      qed
      hence False 
        by (simp add: assms(10))
    }
    thus ?thesis 
      using Par_def \<open>Y B Par E Z\<close> by auto
  qed
  {
    assume "Col A' D' E'"
    have "Col A' B' D'" 
      by (metis (full_types) \<open>Col A' D' E'\<close> \<open>Col E' A' B'\<close> \<open>Col E' E Z\<close> 
          \<open>X A Par E Z\<close> \<open>X A ParStrict E Z\<close> assms(4) col2__eq col_permutation_3 
          col_permutation_4 not_strict_par2 par_strict_not_col_4)
    have "Col A' X A" 
      using Col_cases assms(4) by blast
    moreover have "Col A' Y B"
    proof -
      have "Col Y B' D'" 
        using assms(7) assms(8) assms(2) col_transitivity_1 by blast
      have "A D Par A B" 
        using \<open>Col A' B' D'\<close> assms(14) assms(15) not_par_one_not_par par_col_par 
          par_distinct by blast
      hence False 
        by (meson assms(6) assms(10) assms(12) l6_16_1 one_side_not_col124 
            par_id_3 pars__os3412)
      thus ?thesis
        by blast
    qed
    ultimately have False 
      using assms(12) par_not_col by blast
  }
  have "\<not> Col X A B" 
    using assms(12) par_strict_not_col_4 by auto
  hence "B \<noteq> B'" 
    by (metis Col_cases assms(4) assms(11) assms(14) 
        col2__eq inter__npar inter_trivial)
  hence "C \<noteq> C'" 
    by (metis Col_cases Par_cases assms(5) assms(7) assms(12) assms(16) colx 
        not_col_distincts par_id_5 par_not_col)
  have "\<not> Col Y A B" 
    using assms(12) col_permutation_4 par_strict_not_col_2 by blast
  have "D \<noteq> D'" 
    by (metis Col_cases assms(4) assms(8) assms(11) assms(12) assms(15) colx 
        inter__npar inter_trivial not_col_distincts par_not_col)
  have "A' \<noteq> C'" 
    using \<open>\<not> Col X A B\<close> assms(9) assms(14) assms(16) assms(3) l6_16_1 
      not_par_one_not_par par_comm par_id by blast
  have "B' \<noteq> D'" 
    using Col_cases \<open>Col A' D' E' \<Longrightarrow> False\<close> \<open>Col E' A' B'\<close> by blast
  have "A \<noteq> E" 
    using \<open>Col A D E \<Longrightarrow> False\<close> col_trivial_3 by force
  have "A' \<noteq> E'" 
    using \<open>Col A' D' E' \<Longrightarrow> False\<close> col_trivial_3 by blast
  have "B \<noteq> E" 
    using \<open>Y B ParStrict E Z\<close> col_trivial_2 par_strict_not_col_1 by blast
  have "B' \<noteq> E'" 
    using \<open>Col E' E Z\<close> \<open>Y B ParStrict E Z\<close> assms(7) col_permutation_2 par_not_col by blast
  have "A E Par A' E'" 
    by (metis \<open>A \<noteq> E\<close> \<open>A' \<noteq> E'\<close> \<open>Col E A B\<close> \<open>Col E' A' B'\<close> assms(14) col_par 
        not_par_one_not_par par_left_comm par_neq2 par_trans)
  have "A E ParStrict A' E'" 
    by (metis NCol_perm \<open>A E Par A' E'\<close> \<open>X A ParStrict E Z\<close> assms(4) 
        assms(11) col_trivial_3 l6_16_1 par_not_col_strict 
        par_strict_not_col_1)
  have "D E Par D' E'" 
  proof (rule l13_15_par [where ?A="A" and ?A'="A'"])
    show "\<not> Col A D E" 
      using \<open>Col A D E \<Longrightarrow> False\<close> by auto
    show "A D ParStrict A' D'" 
      by (metis NCol_perm Par_def \<open>D \<noteq> D'\<close> assms(6) assms(8) assms(12) assms(15) 
          colx par_strict_comm par_strict_not_col_3)
    show "A E ParStrict A' E'" 
      using \<open>A E ParStrict A' E'\<close> by auto
    show "A A' Par D D'" 
      by (meson \<open>D \<noteq> D'\<close> \<open>X A Par E Z\<close> \<open>Y B Par E Z\<close> assms(4) assms(6) assms(8) 
          assms(11) not_col_distincts not_par_one_not_par par_col4__par)
    have "A X Par E E'" 
      by (metis \<open>A E ParStrict A' E'\<close> \<open>Col E' E Z\<close> \<open>X A Par E Z\<close> not_col_distincts 
          par_col2_par_bis par_comm par_strict_not_col_2)
    thus "A A' Par E E'" 
      using Col_cases assms(4) assms(11) par_col_par_2 by blast
  qed
  have "C E Par C' E'" 
  proof (rule l13_15_par [where ?A="B" and ?A'="B'"])
    show "\<not> Col B C E" 
      by (metis \<open>B \<noteq> E\<close> \<open>Col E A B\<close> \<open>\<not> Col X A B\<close> assms(9) assms(3) 
          col_permutation_5 col_trivial_3 colx l6_16_1)
    show "B C ParStrict B' C'" 
      by (metis NCol_perm Par_def \<open>B \<noteq> B'\<close> assms(5) assms(7) assms(12) assms(16) 
          l6_16_1 par_not_col)
    show "B E ParStrict B' E'" 
    proof -
      have "B A Par B' E'" 
        by (metis Col_cases Par_cases \<open>B' \<noteq> E'\<close> \<open>Col E' A' B'\<close> assms(14) par_col_par)
      hence "B E Par B' E'" 
        using Col_cases \<open>B \<noteq> E\<close> \<open>Col E A B\<close> par_col_par_2 by blast
      thus ?thesis 
        by (metis NCol_cases Par_def \<open>A E ParStrict A' E'\<close> \<open>Col E' A' B'\<close> 
            l6_16_1 par_strict_not_col_2)
    qed
    show "B B' Par C C'" 
      by (metis Par_def Par_perm \<open>B \<noteq> B'\<close> \<open>C \<noteq> C'\<close> assms(1) assms(5) assms(7)
          assms(12) assms(2) assms(3) col_par not_col_permutation_2 par_trans)
    have "B Y Par E E'" 
      by (metis \<open>A E ParStrict A' E'\<close> \<open>Col E' E Z\<close> \<open>Y B Par E Z\<close> not_col_distincts 
          par_col2_par_bis par_comm par_strict_not_col_2)
    thus "B B' Par E E'" 
      using Col_cases \<open>B \<noteq> B'\<close> assms(7) par_col_par_2 by blast
  qed
  have "C \<noteq> D" 
    using Col_cases assms(6) assms(12) assms(3) par_not_col by blast
  moreover have "C E Par C' D'" 
  proof -
    have "C' \<noteq> D'" 
      using Col_cases assms(5) assms(8) assms(12) par_not_col by blast
    moreover have "Col C' E' D'" 
    proof (rule col_par_par_col [where ?A="C" and ?B="E" and ?C="D"])
      show "Col C E D" 
        using Col_cases \<open>Col E C D\<close> by auto
      show "C E Par C' E'" 
        using \<open>C E Par C' E'\<close> by blast
      show "E D Par E' D'" 
        using Par_cases \<open>D E Par D' E'\<close> by blast
    qed
    moreover have "C' E' Par C E" 
      using Par_cases \<open>C E Par C' E'\<close> by blast
    ultimately show ?thesis 
      using \<open>C E Par C' E'\<close> par_col_par by blast
  qed
  ultimately show ?thesis 
    using par_col_par_2 \<open>Col E C D\<close> col_permutation_4 by blast
qed

lemma (in Tarski_Euclidean) l13_19_par:
  assumes "X \<noteq> A" and
    "X \<noteq> A'" and 
  (*"X \<noteq> C" and 
    "X \<noteq> C'" and *) 
    "Y \<noteq> B" and 
    "Y \<noteq> B'" and
  (*"Y \<noteq> D" and
    "Y \<noteq> D'" and *)
    "Col X A C" and
    "Col X A A'" and
    "Col X A C'" and
    "Col Y B D" and
    "Col Y B B'" and
    "Col Y B D'" and
    "X A ParStrict Y B" and
    "A B Par A' B'" and
    "A D Par A' D'" and
    "B C Par B' C'"
  shows "C D Par C' D'" 
proof (cases "A = C")
  case True
  have "A' B' Par B' C'" 
    using Par_cases True assms(12) assms(14) par_trans by blast
  moreover have "A' B' ParStrict B' C' \<longrightarrow> ?thesis" 
    using Par_strict_cases not_par_strict_id by blast
  ultimately show ?thesis 
    by (metis Par_def True assms(6) assms(7) assms(9) assms(11) assms(13) 
        colx not_col_permutation_1 par_not_col)
next
  case False
  hence "A \<noteq> C"
    by simp
  show ?thesis 
  proof (cases "B = D")
    case True
    have "A' B' Par A' D'" 
      using True assms(12) assms(13) not_par_one_not_par par_symmetry by blast
    moreover have "A' B' ParStrict A' D' \<longrightarrow> ?thesis" 
      using not_par_strict_id by blast
    ultimately show ?thesis 
      by (metis True assms(6) assms(9) assms(10) assms(11) assms(14) colx 
          not_col_permutation_1 par_id_4 par_left_comm par_not_col par_right_comm)
  next
    case False
    hence "B \<noteq> D"
      by simp
    show ?thesis 
    proof (cases "A = A'")
      case True
      hence "A B ParStrict A' B' \<longrightarrow> ?thesis" 
        by (simp add: not_par_strict_id)
      moreover {
        assume "A \<noteq> B" and "A \<noteq> B'" and "Col A A B'" and "Col B A B'"
        have "B = B'" 
          by (metis Par_strict_cases True assms(9) assms(11) assms(12) 
              col2__eq par_id par_strict_not_col_2)
        hence "C = C'" 
          by (metis assms(7) assms(11) assms(14) assms(5) colx par_id_4 
              par_strict_not_col_4)
        moreover have "D = D'" 
          by (metis Par_strict_cases True assms(8) assms(10) assms(11) 
              assms(13) colx par_id_4 par_strict_not_col_1)
        ultimately have ?thesis 
          by (metis assms(7) assms(10) assms(11) not_col_permutation_1 
              par_not_col par_reflexivity)
      }
      ultimately show ?thesis 
        using True assms(12) col_trivial_1 par_distinct par_id_1 by force
    next
      case False
      hence "A \<noteq> A'"
        by simp
      show ?thesis 
      proof (cases "C D Par C' D'")
        case True
        then show ?thesis 
          by simp
      next
        case False
        hence "\<not> C D Par C' D'"
          by simp
        have "\<not> C D Par A B \<or> \<not> C' D' Par A B" 
          using False not_par_one_not_par by blast
        moreover have "\<not> C D Par A B \<longrightarrow> ?thesis" 
          by (meson \<open>A \<noteq> A'\<close> \<open>A \<noteq> C\<close> \<open>B \<noteq> D\<close> assms(1) assms(6) assms(7) 
              assms(8) assms(9) assms(10) assms(11) assms(12) assms(13) assms(14) assms(3) 
              assms(5) l13_19_par_aux par_symmetry)
        moreover {
          assume "\<not> C' D' Par A B"  
          have "A' \<noteq> B'" 
            using assms(12) par_neq2 by auto
          {
            assume "A' = C'"
            have "\<not> Col X A B" 
              using assms(11) par_strict_not_col_4 by auto
            moreover have "Col B A C" 
              using Par_cases \<open>A' = C'\<close> assms(12) assms(14) par_id_3 
                postulate_of_transitivity_of_parallelism_def 
                postulate_of_transitivity_of_parallelism_thm by blast
            ultimately have "A = C" 
              using assms(5) l6_16_1 by blast
            hence False 
              using \<open>A \<noteq> C\<close> by auto
          }
          moreover {
            assume "B' = D'" 
            hence "A D Par A B" 
              using \<open>B' = D'\<close> assms(12) assms(13) not_par_one_not_par by blast
            have "\<not> Col Y B A" 
              using assms(11) col_permutation_2 par_strict_not_col_2 by blast
            moreover have "Col A B D" 
              using \<open>A D Par A B\<close> par_id_3 by auto
            ultimately have False 
              using \<open>B \<noteq> D\<close> assms(8) col2__eq by blast
          }
          moreover have "A' \<noteq> A" 
            using \<open>A \<noteq> A'\<close> by auto
          moreover have "Col X A' C'" 
            using assms(1) assms(6) assms(7) col_transitivity_1 by blast
          moreover have "Col X A' A" 
            using Col_cases assms(6) by auto
          moreover have "Col X A' C" 
            using assms(1) assms(6) assms(5) col_transitivity_1 by blast
          moreover have "Col Y B' D'" 
            using assms(9) assms(10) assms(3) col_transitivity_1 by blast
          moreover have "Col Y B' B" 
            using Col_cases assms(9) by auto
          moreover have "Col Y B' D" 
            using assms(8) assms(9) assms(3) col_transitivity_1 by blast
          moreover have "X A' ParStrict Y B'" 
            by (meson assms(4) assms(9) assms(11) assms(2) assms(6) 
                not_col_distincts par_strict_col4__par_strict)
          moreover have "\<not> A' B' Par C' D'" 
            using Par_cases \<open>\<not> C' D' Par A B\<close> assms(12) par_trans by blast
          moreover have "A' B' Par A B" 
            using Par_cases assms(12) by blast
          moreover have "A' D' Par A D" 
            using Par_cases assms(13) by blast
          moreover have "B' C' Par B C" 
            using Par_cases assms(14) by blast
          ultimately have "C' D' Par C D" 
            using l13_19_par_aux assms(1) assms(6) assms(7) assms(8) 
              assms(9) assms(10) assms(2) assms(3) assms(4) assms(5) by presburger
          hence ?thesis 
            using Par_cases by blast
        }
        ultimately show ?thesis 
          by blast
      qed
    qed
  qed
qed

end