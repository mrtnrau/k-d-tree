theory Test
  imports Complex_Main "HOL-Library.Tree"
begin

lemma A0:
  "l \<le> r \<Longrightarrow> r - l \<le> 1 \<Longrightarrow> l = r \<or> l + 1 = r" for l :: nat and r :: nat
  by auto

lemma min_height_height_if_balanced:
  "balanced t \<Longrightarrow> min_height t + 1 = height t \<or> min_height t = height t"
  unfolding balanced_def using min_height_le_height A0 by blast

lemma AUX1:
  assumes "(2 :: nat) ^ x + 1 = 2 ^ y"
  shows "x = 0"
proof (rule ccontr)
  assume "\<not>(x = 0)"
  hence "odd ((2 :: nat) ^ x + 1)"
    by simp
  moreover have "(2 :: nat) ^ x > 0"
    by simp
  hence "even ((2 :: nat) ^ y)"
    using div_eq_0_iff assms by fastforce
  ultimately show False using assms by metis
qed

lemma AUX2:
  assumes "(2 :: nat) ^ x + 1 = 2 ^ y"
  shows "y = 1"
proof -
  have "(2 :: nat) = 2 ^ y"
    using assms AUX1 by force
  thus ?thesis by (cases y) auto
qed

lemma B3:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l < min_height r"
  shows "min_height l + 1 = min_height r"
proof cases
  assume *: "complete l"
  thus ?thesis
  proof cases
    assume "complete r"
    hence "2 ^ min_height l = size1 l" "size1 r = 2 ^ min_height r"
      using * by (simp add: complete_iff_height size1_if_complete)+
    hence "(2 :: nat) ^ min_height l + 1 = 2 ^ min_height r"
      using assms(1) by simp
    hence "min_height l = 0" "min_height r = 1"
      using AUX1[of "min_height l" "min_height r"] AUX2[of "min_height l" "min_height r"] by simp_all
    thus ?thesis by simp
  next
    assume **: "\<not>complete r"
    hence "2 ^ min_height r < size1 r"
      using min_height_size1_if_incomplete by blast
    also have "... = size1 l + 1"
      using assms(1) by auto
    also have "... = 2 ^ (min_height l) + 1"
      by (metis * complete_iff_height size1_if_complete)
    finally have "(2 :: nat) ^ min_height r < 2 ^ (min_height l) + 1" .
    hence "(2 :: nat) ^ min_height r \<le> 2 ^ min_height l"
      by linarith
    moreover have "(2 :: nat) ^ min_height l < 2 ^ min_height r"
      by (simp add: assms(4))
    ultimately have "False"
      by auto
    thus ?thesis by simp
  qed
next
  assume *: "\<not>complete l"
  have "2 ^ min_height r \<le> size1 r"
    by (simp add: min_height_size1)
  also have "... = size1 l + 1"
    using assms(1) by simp
  also have "... \<le> 2 ^ height l"
    using * discrete size1_height_if_incomplete by blast
  also have "... = (2 :: nat) ^ (min_height l + 1)"
    using * assms(2) complete_iff_height min_height_height_if_balanced by fastforce
  finally have "2 ^ min_height r \<le> (2 :: nat) ^ (min_height l + 1)" by simp
  hence "min_height r \<le> min_height l + 1"
    using one_less_numeral_iff power_le_imp_le_exp semiring_norm(76) by blast
  thus ?thesis
    using assms(4) by linarith
qed

lemma B4:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l + 1 = min_height r"
  shows "complete r"
proof -
  consider (A) "complete r" | (B) "\<not>complete r \<and> complete l" | (C) "\<not>complete r \<and> \<not>complete l"
    by blast
  then show ?thesis
  proof cases
    case A
    thus ?thesis by simp
  next
    case B
    hence "2 ^ min_height r < size1 r"
      using min_height_size1_if_incomplete by blast
    also have "... = size1 l + 1"
      using assms(1) by auto
    also have "... = 2 ^ (min_height l) + 1"
      by (metis B complete_iff_height size1_if_complete)
    finally have "(2 :: nat) ^ min_height r < 2 ^ (min_height l) + 1" .
    hence "(2 :: nat) ^ min_height r \<le> 2 ^ min_height l"
      by linarith
    moreover have "(2 :: nat) ^ min_height l < 2 ^ min_height r"
      using assms(4) by auto
    ultimately have "False"
      by auto
    then show ?thesis by simp
  next
    case C
    have "size1 r = size1 l + 1"
      using assms(1) by simp
    also have "... \<le> 2 ^ height l"
      using C discrete size1_height_if_incomplete by blast
    also have "... = 2 ^ (min_height r)"
      using C assms(2,4) complete_iff_height min_height_height_if_balanced by force
    finally have "size1 r \<le> 2 ^ min_height r" .
    moreover have "2 ^ min_height r < size1 r"
      by (simp add: C min_height_size1_if_incomplete)
    ultimately have "False" by simp
    then show ?thesis by simp
  qed
qed

lemma B5:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r" "min_height l + 1 = min_height r"
  shows "balanced (Node l x r)"
proof -
  have *: "complete r"
    using assms B4 by blast
  thus ?thesis
  proof (cases "complete l")
    case True
    hence "2 ^ min_height l = size1 l" "size1 r = 2 ^ min_height r"
      using * by (simp add: complete_iff_height size1_if_complete)+
    hence "(2 :: nat) ^ min_height l + 1 = 2 ^ min_height r"
      using assms(1) by simp
    hence "min_height l = 0" "min_height r = 1"
      using AUX1[of "min_height l" "min_height r"] AUX2[of "min_height l" "min_height r"] by simp_all
    thus ?thesis using balanced_def * True complete_iff_height by force
  next
    case False
    then show ?thesis sorry
  qed
qed

lemma A:
  assumes "size1 l = size1 r" "balanced l" "balanced r"
  shows "balanced (Node l x r)"
proof -
  have "height l \<le> height r"
    using assms(1,2) balanced_optimal[of l r] by (simp add: size1_def)
  moreover have "height r \<le> height l"
    using assms(1,3) balanced_optimal[of r l] by (simp add: size1_def)
  ultimately have "height l = height r"
    by simp
  moreover have "min_height l = height l \<or> min_height l + 1 = height l"
    using assms(2) min_height_height_if_balanced by blast
  moreover have "min_height r = height r \<or> min_height r + 1 = height r"
    using assms(3) min_height_height_if_balanced by blast
  ultimately show ?thesis by (auto simp add: balanced_def)
qed

lemma B:
  assumes "size1 l + 1 = size1 r" "balanced l" "balanced r"
  shows "balanced (Node l x r)"
proof (cases "min_height l = min_height r")
  case True
  then show ?thesis using assms unfolding balanced_def
    by (auto simp add: min_def max_def)
next
  case False
  have "(2 ::nat) ^ min_height l <  2 ^ height r"
    using assms(1) min_height_size1 size1_height discrete by (metis le_less_trans)
  hence "min_height l < height r"
    using nat_power_less_imp_less pos2 by blast
  hence "min_height l < min_height r"
    using assms(3) False min_height_height_if_balanced by fastforce
  thus ?thesis by (meson B3 B5 assms le_less)
qed

end