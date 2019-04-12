theory Priority
  imports Main
begin

datatype 'a pq = PQ nat "'a list"

fun pq_invar :: "'a :: linorder pq \<Rightarrow> bool" where
  "pq_invar (PQ m pq) \<longleftrightarrow> distinct pq \<and> sorted pq \<and> length pq \<le> m"

fun pq_size :: "'a pq \<Rightarrow> nat" where
  "pq_size (PQ _ pq) = length pq"

fun pq_max :: "'a pq \<Rightarrow> 'a" where
  "pq_max (PQ _ pq) = pq ! (length pq - 1)"

fun pq_insert :: "'a :: linorder \<Rightarrow> 'a pq \<Rightarrow> 'a pq" where
  "pq_insert a (PQ m pq) = PQ m (take m (insort a pq))"

fun pq_insert_many :: "'a :: linorder list \<Rightarrow> 'a pq \<Rightarrow> 'a pq" where
  "pq_insert_many as pq = foldl (\<lambda>pq a. pq_insert a pq) pq as"

fun pq_list :: "'a pq \<Rightarrow> 'a list" where
  "pq_list (PQ _ pq) = pq"

fun pq_set :: "'a pq \<Rightarrow> 'a set" where
  "pq_set (PQ _ pq) = set pq"




lemma size_pq:
  "pq_invar (PQ m pq) \<Longrightarrow> pq_size (PQ m pq) \<le> m"
  by simp

lemma AUX0:
  "set xs = (\<lambda>i. xs!i) ` { i. i < length xs }"
  apply (induction xs)
   apply (auto)
  using image_iff apply fastforce
  using mem_Collect_eq apply force
  by (metis insert_iff length_Cons list.set(2) nth_mem)

lemma AUX:
  "\<forall>i \<le> (length xs - 1). xs!i \<le> m \<Longrightarrow> \<forall>x \<in> set xs. x \<le> m"
  by (simp add: AUX0)

lemma pq_max:
  assumes "pq = PQ m l" "pq_invar pq"
  shows "\<forall>x \<in> pq_set pq. x \<le> pq_max pq"
proof -
  have "sorted l"
    using assms by simp
  hence "\<forall>i \<le> (length l - 1). l!i \<le> l!(length l - 1)"
    using sorted_nth_mono by fastforce
  moreover have "pq_max pq = l!(length l - 1)"
    using assms(1) by simp
  ultimately show ?thesis
    using AUX assms(1) by auto
qed

end