theory Test
  imports Complex_Main "HOL-Library.Tree"
begin

lemma min_height_height_if_balanced:
  "balanced t \<Longrightarrow> min_height t + 1 = height t \<or> min_height t = height t"
  by (metis balanced_def One_nat_def Suc_eq_plus1 diff_diff_cancel diff_zero le_SucE le_add_diff_inverse le_zero_eq min_height_le_height)

lemma B1:
  assumes "size1 l + 1 = size1 r" "balanced r"
  shows "min_height l \<le> min_height r"
proof -
  have "(2 ::nat) ^ min_height l \<le> size1 l"
    using min_height_size1 by blast
  also have "... < size1 r"
    using assms(1) by simp
  also have "... \<le> 2 ^ height r"
    using size1_height by blast
  finally have "(2 :: nat) ^ min_height l < 2 ^ height r" .
  hence "min_height l < height r"
    using nat_power_less_imp_less pos2 by blast
  moreover have "min_height r + 1 = height r \<or> min_height r = height r"
    using assms(2) min_height_height_if_balanced by auto
  ultimately show ?thesis by auto
qed

lemma B2:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l = min_height r"
  shows "balanced (Node l x r)"
  using assms unfolding balanced_def
  apply (auto simp add: min_def max_def)
  done

lemma AUX1:
  assumes "(2 :: nat) ^ x + 1 = 2 ^ y"
  shows "x = 0"
proof (rule ccontr)
  assume "\<not>(x = 0)"
  hence "x > 0"
    by simp
  hence "even ((2 :: nat) ^ x)"
    by simp
  hence "odd ((2 :: nat) ^ x + 1)"
    by simp
  moreover have "(2 :: nat) ^ x > 0"
    by simp
  hence "(2 :: nat) ^ y > 1"
    using assms by linarith
  hence "even ((2 :: nat) ^ y)"
    using div_eq_0_iff by fastforce
  ultimately show False using assms by metis
qed

lemma AUX3:
  "(2 :: nat) = 2 ^ y \<Longrightarrow> y = 1"
  apply (induction y)
   apply (auto)
  done

lemma AUX2:
  assumes "(2 :: nat) ^ x + 1 = 2 ^ y"
  shows "y = (1 :: nat)"
proof -
  have "(2 :: nat) = 2 ^ y"
    using assms AUX1 by force
  hence "y = 1"
    using AUX3 by simp
  thus ?thesis by simp
qed

lemma B3:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l < min_height r"
  shows "min_height l + 1 = min_height r"
proof -
  consider (A) "complete r \<and> complete l" | (B) "complete r \<and> \<not>complete l" | (C) "\<not>complete r \<and> complete l" | (D) "\<not>complete r \<and> \<not>complete l"
    by blast
  then show ?thesis
  proof cases
    case A
    hence "2 ^ min_height l = size1 l" "size1 r = 2 ^ min_height r"
      by (simp add: complete_iff_height size1_if_complete)+
    hence "(2 :: nat) ^ min_height l + 1 = 2 ^ min_height r"
      using assms(1) by simp
    hence "min_height l = 0" "min_height r = 1"
      using AUX1[of "min_height l" "min_height r"] AUX2[of "min_height l" "min_height r"] by simp_all
    then show ?thesis by simp
  next
    case B
    hence "2 ^ min_height r = size1 r"
      using complete_iff_height size1_if_complete by force
    also have "... = size1 l + 1"
      using assms(1) by simp
    also have "... \<le> 2 ^ height l"
      using B discrete size1_height_if_incomplete by blast
    also have "... = (2 :: nat) ^ (min_height l + 1)"
      using B assms(2) complete_iff_height min_height_height_if_balanced by fastforce
    finally have "2 ^ min_height r \<le> (2 :: nat) ^ (min_height l + 1)" by simp
    hence "min_height r \<le> min_height l + 1"
      using one_less_numeral_iff power_le_imp_le_exp semiring_norm(76) by blast
    then show ?thesis using assms(4) by simp
  next
    case C
    hence "2 ^ min_height r < size1 r"
      using min_height_size1_if_incomplete by blast
    also have "... = size1 l + 1"
      using assms(1) by auto
    also have "... = 2 ^ (min_height l) + 1"
      by (metis C complete_iff_height size1_if_complete)
    finally have "(2 :: nat) ^ min_height r < 2 ^ (min_height l) + 1" .
    hence "(2 :: nat) ^ min_height r \<le> 2 ^ min_height l"
      by linarith
    moreover have "(2 :: nat) ^ min_height l < 2 ^ min_height r"
      by (simp add: assms(4))
    ultimately have "False"
      by auto
    then show ?thesis by simp
  next
    case D
    hence "2 ^ min_height r \<le> size1 r"
      using min_height_size1 by blast
    also have "... = size1 l + 1"
      using assms(1) by simp
    also have "... \<le> 2 ^ height l"
      using D discrete size1_height_if_incomplete by blast
    also have "... = (2 :: nat) ^ (min_height l + 1)"
      using D assms(2) complete_iff_height min_height_height_if_balanced by fastforce
    finally have "2 ^ min_height r \<le> (2 :: nat) ^ (min_height l + 1)" by simp
    hence "min_height r \<le> min_height l + 1"
      using one_less_numeral_iff power_le_imp_le_exp semiring_norm(76) by blast
    then show ?thesis using assms(4) by simp
  qed
qed

lemma B4:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l + 1 = min_height r"
  shows "min_height r = height r"
proof -
  consider (A) "complete r \<and> complete l" | (B) "complete r \<and> \<not>complete l" | (C) "\<not>complete r \<and> complete l" | (D) "\<not>complete r \<and> \<not>complete l"
    by blast
  then show ?thesis
  proof cases
    case A
    then show ?thesis
      using complete_iff_height by blast
  next
    case B
    then show ?thesis using assms
      using complete_iff_height by blast
  next
    case C
    hence "2 ^ min_height r < size1 r"
      using min_height_size1_if_incomplete by blast
    also have "... = size1 l + 1"
      using assms(1) by auto
    also have "... = 2 ^ (min_height l) + 1"
      by (metis C complete_iff_height size1_if_complete)
    finally have "(2 :: nat) ^ min_height r < 2 ^ (min_height l) + 1" .
    hence "(2 :: nat) ^ min_height r \<le> 2 ^ min_height l"
      by linarith
    moreover have "(2 :: nat) ^ min_height l < 2 ^ min_height r"
      using assms(4) by auto
    ultimately have "False"
      by auto
    then show ?thesis by simp
  next
    case D
    have "size1 r = size1 l + 1"
      using assms(1) by simp
    also have "... \<le> 2 ^ height l"
      using D discrete size1_height_if_incomplete by blast
    also have "... = 2 ^ (min_height r)"
      using D assms(2,4) complete_iff_height min_height_height_if_balanced by force
    finally have "size1 r \<le> 2 ^ min_height r" .
    moreover have "2 ^ min_height r < size1 r"
      by (simp add: D min_height_size1_if_incomplete)
    ultimately have "False" by simp
    then show ?thesis by simp
  qed
qed

lemma B5:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l + 1 = min_height r"
  shows "balanced (Node l x r)"
  using assms unfolding balanced_def
  apply (auto simp add: min_def max_def)
  by (smt One_nat_def B4 add_diff_cancel_left' assms diff_Suc_Suc le_less)

lemma A:
  assumes "size1 l = size1 r" "balanced l" "balanced r"
  shows "balanced (Node l x r)"
  using assms unfolding balanced_def
  apply (auto simp add: min_def max_def)
  apply (metis add_right_cancel assms(3) balanced_optimal leD le_less size1_def)
  by (metis add_right_cancel assms(2) balanced_optimal le_less size1_def)

lemma B:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r"
  shows "balanced (Node l x r)"
  by (meson B1 B2 B3 B5 assms le_less)

end