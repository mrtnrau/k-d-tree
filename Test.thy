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

lemma B3:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l < min_height r"
  shows "min_height l + 1 = min_height r"
proof (cases "complete r")
  case True
  then show ?thesis
    by (metis (no_types, lifting) Suc_eq_plus1 Suc_leI assms(1) assms(2) assms(4) complete_if_size1_height complete_iff_height leD le_less less_Suc_eq min_height_height_if_balanced one_less_numeral_iff power_strict_increasing_iff semiring_norm(76) size1_height size1_if_complete)
next
  case False
  then show ?thesis
    by (smt Suc_eq_plus1 Suc_leI assms(1) assms(2) assms(4) leD le_less le_less_trans min_height_height_if_balanced min_height_size1_if_incomplete one_less_numeral_iff power_strict_increasing_iff semiring_norm(76) size1_height_if_incomplete size1_if_complete)
qed

lemma B4:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l + 1 = min_height r"
  shows "min_height r = height r"
proof (cases "complete l")
  case True
  then show ?thesis
    by (metis Suc_eq_plus1 assms(1) assms(4) complete_iff_height less_Suc_eq min_height_size1_if_incomplete not_add_less1 power_strict_increasing_iff rel_simps(49) rel_simps(9) size1_if_complete)
next
case False
  then show ?thesis
    by (metis Suc_eq_plus1 Suc_leI assms(1) assms(2) assms(4) complete_if_size1_min_height le_antisym min_height_height_if_balanced min_height_size1 power_inject_exp rel_simps(49) rel_simps(9) size1_height size1_height_if_incomplete size1_if_complete)
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