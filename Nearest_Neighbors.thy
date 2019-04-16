theory Nearest_Neighbors
  imports Complex_Main KDTree
begin

text \<open>
  Verifying nearest neighbor search on the k-d tree.

  Given k-d tree and a point p, which might not be in the tree, find the point p' which is
  closest to p by some metric.

  The chosen metric is the euclidean distance between two points.

  To avoid working with roots I will work with the squared euclidean distance.
\<close>

text \<open>Definitions and lemmas about the squared euclidean distance.\<close>

definition sqed' :: "real \<Rightarrow> real \<Rightarrow> real" where
  "sqed' x y = (x - y) ^ 2"

fun sqed :: "point \<Rightarrow> point \<Rightarrow> real" where
  "sqed [] [] = 0"
| "sqed (x # xs) (y # ys) = sqed' x y + sqed xs ys"
| "sqed _ _ = undefined"

definition min_by_sqed :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point" where
  "min_by_sqed p\<^sub>0 p\<^sub>1 q = (
    if sqed p\<^sub>0 q \<le> sqed p\<^sub>1 q then p\<^sub>0 else p\<^sub>1
  )"

lemma sqed'_ge_0:
  "0 \<le> sqed' x y"
  by (simp add: sqed'_def)

lemma sqed'_eq_0[simp]:
  "sqed' x y = 0 \<longleftrightarrow> x = y"
  by (simp add: sqed'_def)

lemma sqed'_com:
  "sqed' x y = sqed' y x"
  by (simp add: sqed'_def power2_commute)

lemma inequality:
  assumes "(x::real) \<le> 0" "y \<le> 0"
  shows "x\<^sup>2 + y\<^sup>2 \<le> (x + y)\<^sup>2"
proof -
  have "x\<^sup>2 + y\<^sup>2 \<le> x\<^sup>2 + 2 * x * y + y\<^sup>2"
    using assms by (simp add: zero_le_mult_iff)
  also have "... = (x + y)\<^sup>2"
    by algebra
  finally show ?thesis .
qed

lemma sqed'_split:
  "x \<le> s \<Longrightarrow> s \<le> y \<Longrightarrow> sqed' x s + sqed' s y \<le> sqed' x y"
  using sqed'_def inequality by smt

lemma sqed_ge_0:
  "dim p\<^sub>0 = dim p\<^sub>1 \<Longrightarrow> 0 \<le> sqed p\<^sub>0 p\<^sub>1"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_ge_0)

lemma sqed_eq_0[simp]:
  "p\<^sub>0 = p\<^sub>1 \<Longrightarrow> sqed p\<^sub>0 p\<^sub>1 = 0"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) auto

lemma sqed_eq_0_rev:
  "dim p\<^sub>0 = dim p\<^sub>1 \<Longrightarrow> sqed p\<^sub>0 p\<^sub>1 = 0 \<Longrightarrow> p\<^sub>0 = p\<^sub>1"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: add_nonneg_eq_0_iff sqed'_ge_0 sqed_ge_0)

lemma sqed_com:
  "sqed p\<^sub>0 p\<^sub>1 = sqed p\<^sub>1 p\<^sub>0"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_com)




text\<open>The nearest neighbor algorithm.\<close>

fun nearest_neighbor :: "point \<Rightarrow> kdt \<Rightarrow> point" where
  "nearest_neighbor _ (Leaf p) = p"
| "nearest_neighbor p (Node a s l r) = (
    if p!a \<le> s then
      let candidate = nearest_neighbor p l in
      if sqed p candidate \<le> sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor p r in
        min_by_sqed candidate candidate' p
    else
      let candidate = nearest_neighbor p r in
      if sqed p candidate \<le> sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor p l in
        min_by_sqed candidate candidate' p
  )"




text \<open>First part of main theorem.\<close>

lemma nearest_neighbor_in_kdt:
  "nearest_neighbor p kdt \<in> set_kdt kdt"
  by (induction kdt) (auto simp add: Let_def min_by_sqed_def)




text \<open>Second part of main theorem.\<close>

text \<open>Auxiliary lemmas.\<close>

text \<open>
  Some intuition about this step:

  Scenario A:
  We are searching for the nearest neighbor of point p and have found candidate c at axis a.
  Since sqed c p <= sqed' s (p!a) we do not need to check the right side.

                                s
          c                     |
                                |
               p                |
                                |
                                |  q
                                |


  Scenario B:
  We are searching for the nearest neighbor of point p and have found candidate c at axis a.
  Since sqed' s (p!a) < sqed c p  we do need to check the right side.

                                s
          c                     |
                                |
                          p     |  q'
                                |
                                |  q
                                |

  The minimize_sqed lemma moves q to q' by setting all coordinates of q' (except the current axis a)
  to the coordinates of p and minimizes the distance between p and q'.
\<close>

lemma minimize_sqed:
  assumes "dim p\<^sub>0 = k" "dim p\<^sub>1 = k" "a < k"
  shows "sqed' (p\<^sub>0!a) (p\<^sub>0[a := (p\<^sub>1!a)]!a) \<le> sqed p\<^sub>0 p\<^sub>1"
  using assms
  apply (induction p\<^sub>0 p\<^sub>1 arbitrary: a k rule: sqed.induct)
  apply (auto simp add: sqed_ge_0 split: nat.splits)
  by (smt sqed'_ge_0)

lemma cutoff_r:
  assumes "invar k (Node a s l r)" "dim p = k"
  assumes "p!a \<le> s" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt r. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume *: "q \<in> set_kdt r"

  let ?q' = "p[a := (q!a)]"

  have "sqed' (p!a) (?q'!a) \<le> sqed p q"
    using * minimize_sqed assms(1,2) invar_axis_lt_d invar_dim invar_r by blast
  hence "sqed' (p!a) s + sqed' s (q!a) \<le> sqed p q"
    by (smt * assms(1,2,3) dim_def nth_list_update_eq invar_axis_lt_d invar_r_ge_a sqed'_split)
  hence "sqed p c \<le> sqed p q"
    by (smt assms(4) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed

lemma cutoff_l:
  assumes "invar k (Node a s l r)" "dim p = k"
  assumes "s \<le> p!a" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt l. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume *: "q \<in> set_kdt l"

  let ?q' = "p[a := (q!a)]"

  have "sqed' (p!a) (?q'!a) \<le> sqed p q"
    using * minimize_sqed invar_dim invar_l invar_axis_lt_d assms(1,2) by blast
  hence "sqed' (p!a) s + sqed' s (q!a) \<le> sqed p q"
    by (smt * assms(1,2,3) dim_def invar_axis_lt_d invar_l_le_a nth_list_update_eq sqed'_com sqed'_split)
  hence "sqed p c \<le> sqed p q"
    by (smt assms(4) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed




text \<open>The main theorem.\<close>

lemma nearest_neighbor_minimal:
  assumes "invar k kdt" "dim p = k"
  shows "\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor p kdt) p \<le> sqed q p"
  using assms
proof (induction kdt)
  case (Leaf p)
  thus ?case
    by simp
next
  case (Node a s l r)

  let ?cl = "nearest_neighbor p l"
  let ?cr = "nearest_neighbor p r"

  have IHL: "\<forall>q \<in> set_kdt l. sqed ?cl p \<le> sqed q p"
    using Node.IH(1) Node.prems(1,2) invar_axis_lt_d by auto
  have IHR: "\<forall>q \<in> set_kdt r. sqed ?cr p \<le> sqed q p"
    using Node.IH(2) Node.prems(1,2) invar_axis_lt_d by auto

  consider (A) "p!a \<le> s \<and> sqed p ?cl \<le> sqed' s (p!a)"
         | (B) "p!a \<le> s \<and> \<not>sqed p ?cl \<le> sqed' s (p!a)"
         | (C) "s < p!a \<and> sqed p ?cr \<le> sqed' s (p!a)"
         | (D) "s < p!a \<and> \<not>sqed p ?cr \<le> sqed' s (p!a)"
    by argo
  thus ?case
  proof cases
    case A
    hence "\<forall>q \<in> set_kdt r. sqed p ?cl \<le> sqed p q"
      using Node.prems(1,2) cutoff_r invar_axis_lt_d invar_l nearest_neighbor_in_kdt by blast
    thus ?thesis 
      using A Node.prems IHL by (auto simp add: sqed_com)
  next
    case B
    thus ?thesis 
      using Node.prems IHL IHR by (auto simp add: min_by_sqed_def Let_def)
  next
    case C
    hence "\<forall>q \<in> set_kdt l. sqed p ?cr \<le> sqed p q"
      using Node.prems(1,2) cutoff_l invar_r invar_axis_lt_d nearest_neighbor_in_kdt by smt
    thus ?thesis 
      using C Node.prems IHR by (auto simp add: sqed_com)
  next
    case D
    thus ?thesis 
      using Node.prems IHL IHR by (auto simp add: min_by_sqed_def Let_def)
  qed
qed

theorem nearest_neighbor:
  assumes "invar k kdt" "dim p = k"
  shows "(\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor p kdt) p \<le> sqed q p) \<and> nearest_neighbor p kdt \<in> set_kdt kdt"
  using assms nearest_neighbor_in_kdt nearest_neighbor_minimal invar_axis_lt_d by simp

corollary
  assumes "invar k kdt" "p \<in> set_kdt kdt"
  shows "nearest_neighbor p kdt = p"
  using assms by (smt invar_dim nearest_neighbor sqed_eq_0 sqed_eq_0_rev sqed_ge_0)




text \<open>
  Now generalize the nearest neighbor algorithm to a m nearest neighbor search.  

  Given k-d tree and a point p, which might not be in the tree, find the m closest points ms
  to p by the squared euclidean distance.
\<close>

text\<open>
  The m nearest neighbor algorithm.

  The paper uses a priority queue for the m nearest neighbor candidates.
  I am using a sorted list for simplicity instead.
\<close>

fun m_nearest_neighbors' :: "nat \<Rightarrow> point list \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point list" where
  "m_nearest_neighbors' m ns p (Leaf p') = (
    take m (insort_key (\<lambda>q. sqed q p) p' ns)
  )"
| "m_nearest_neighbors' m ns p (Node a s l r) = (
    if p!a \<le> s then
      let candidates = m_nearest_neighbors' m ns p l in
      if length candidates = m \<and> sqed p (last candidates) \<le> sqed' s (p!a) then
        candidates
      else
        m_nearest_neighbors' m candidates p r
    else
      let candidates = m_nearest_neighbors' m ns p r in
      if length candidates = m \<and> sqed p (last candidates) \<le> sqed' s (p!a) then
        candidates
      else
        m_nearest_neighbors' m candidates p l
  )"




text\<open>Auxiliary lemmas about sorted_wrt for the base cases of the final theorem.\<close>

definition sqed_sorted :: "point \<Rightarrow> point list \<Rightarrow> bool" where
  "sqed_sorted p \<equiv> sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p)"

definition sqed_insort :: "point \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> point list" where
  "sqed_insort p \<equiv> insort_key (\<lambda>q. sqed q p)"

declare sqed_sorted_def[simp] sqed_insort_def[simp]

lemma
  assumes "sorted_wrt f xs"
  shows sorted_wrt_take: "sorted_wrt f (take n xs)"
  and sorted_wrt_drop: "sorted_wrt f (drop n xs)"
proof -
  have "sorted_wrt f (take n xs @ drop n xs)" 
    using assms by simp
  thus "sorted_wrt f (take n xs)" "sorted_wrt f (drop n xs)"
    using sorted_wrt_append by blast+
qed

lemma sqed_sorted_insort:
  "sqed_sorted p ms \<Longrightarrow> sqed_sorted p (sqed_insort p p' ms)"
  apply (induction ms)
  apply (auto)
  by (metis insert_iff le_cases set_insort_key)

lemma sqed_sorted_take_insort:
  assumes "sqed_sorted p ms"
  shows "sqed_sorted p (take m (sqed_insort p p' ms))"
proof -
  have "sqed_sorted p (sqed_insort p p' ms)"
    using assms sqed_sorted_insort by blast
  thus ?thesis 
    using sorted_wrt_take by auto
qed

lemma
  assumes "sqed_sorted p (xs @ [m] @ ys)"
  shows sqed_sorted_prefix: "\<forall>x \<in> set xs. sqed x p \<le> sqed m p"
  and sqed_sorted_suffix: "\<forall>y \<in> set ys. sqed m p \<le> sqed y p"
  using assms sorted_wrt_append by (simp add: sorted_wrt_append)+

lemma sqed_sorted_last:
  assumes "sqed_sorted p ms"
  shows "\<forall>n \<in> set ms. sqed n p \<le> sqed (last ms) p"
proof (cases "ms = []")
  case True
  thus ?thesis by simp
next
  case False
  then obtain ms' m where [simp]:"ms = ms' @ [m]"
    using rev_exhaust by blast
  hence "sqed_sorted p (ms' @ [m])"
    using assms by blast
  thus ?thesis 
    using sqed_sorted_prefix by simp
qed

lemma sqed_sorted_take_mono:
  assumes "sqed_sorted p ms"
  shows "\<forall>n \<in> set ms - set (take m ms). \<forall>n' \<in> set (take m ms). sqed n' p \<le> sqed n p"
proof (cases "length ms \<le> m")
  case True
  thus ?thesis by simp
next
  case False
  hence "ms = (take m ms) @ [ms!m] @ (drop (m+1) ms)"
    using id_take_nth_drop not_less by auto
  then show ?thesis using assms 
    sqed_sorted_prefix[of p "take m ms" "ms!m" "drop (m+1) ms"]
    sqed_sorted_suffix[of p "take m ms" "ms!m" "drop (m+1) ms"]
    by (smt DiffD1 DiffD2 UnE append_Cons append_Nil set_ConsD set_append)
qed

lemma sqed_sorted_take_insort_mono:
  assumes "sqed_sorted p ms"
  shows "\<forall>n \<in> set ms \<union> {p'} - set (take m (sqed_insort p p' ms)). \<forall>n' \<in> set (take m (sqed_insort p p' ms)). sqed n' p \<le> sqed n p"
proof -
  let ?ms' = "sqed_insort p p' ms"
  have "sqed_sorted p ?ms'"
    using assms sqed_sorted_insort by blast
  hence "\<forall>n \<in> set ?ms' - set (take m ?ms'). \<forall>n' \<in> set (take m ?ms'). sqed n' p \<le> sqed n p"
    using sqed_sorted_take_mono by blast
  thus ?thesis 
    by (simp add: set_insort_key)
qed

lemma sqed_sorted_last_take_mono:
  assumes "sqed_sorted p ms" "m \<le> length ms" "0 < m"
  shows "sqed (last (take m ms)) p \<le> sqed (last ms) p"
  using assms by (induction ms arbitrary: m) (auto simp add: take_Cons')

lemma sqed_sorted_last_insort_eq:
  assumes "sqed_sorted p ms" "sqed_insort p p' ms \<noteq> ms @ [p']"
  shows "last (sqed_insort p p' ms) = last ms"
  using assms by (induction ms) (auto)

lemma sqed_sorted_last_take_insort_mono:
  assumes "sqed_sorted p ms" "m \<le> length ms" "0 < m"
  shows "sqed (last (take m (sqed_insort p p' ms))) p \<le> sqed (last ms) p"
proof -
  let ?ms' = "sqed_insort p p' ms"

  show "sqed (last (take m ?ms')) p \<le> sqed (last ms) p"
  proof (cases "?ms' = ms @ [p']")
    case True
    thus ?thesis
      using assms sqed_sorted_last_take_mono by auto
  next
    case False
    hence EQ: "last ?ms' = last ms"
      using sqed_sorted_last_insort_eq assms by simp
    have "sqed (last (take m ?ms')) p \<le> sqed (last ?ms') p"
      using assms sqed_sorted_last_take_mono sqed_sorted_insort by simp
    thus ?thesis
      using EQ by simp
  qed
qed




text\<open>The main lemmas.\<close>

lemma mnn_length:
  "length (m_nearest_neighbors' m ms p kdt) = min m (size_kdt kdt + length ms)"
  by (induction kdt arbitrary: ms) (auto simp add: Let_def)

lemma mnn_length_gt_0:
  assumes "0 < m"
  shows "0 < length (m_nearest_neighbors' m ms p kdt)"
  using assms by (induction kdt arbitrary: ms) (auto simp add: Let_def)

lemma mnn_length_gt_eq_m:
  assumes "(set_kdt kdt \<union> set ms) - set (m_nearest_neighbors' m ms p kdt) \<noteq> {}"
  shows "length (m_nearest_neighbors' m ms p kdt) = m"
  using assms mnn_length set_insort_key
  apply (induction kdt arbitrary: ms)
  apply (auto simp add: min_def Let_def)
  by fastforce+

lemma mnn_sorted:
  assumes "sqed_sorted p ms"
  shows "sqed_sorted p (m_nearest_neighbors' m ms p kdt)"
  using assms sqed_sorted_take_insort
  by (induction kdt arbitrary: ms) (auto simp add: Let_def)

lemma mnn_set:
  shows "set (m_nearest_neighbors' m ms p kdt) \<subseteq> set_kdt kdt \<union> set ms"
  using set_insort_key in_set_takeD
  apply (induction kdt arbitrary: ms)
  apply (auto simp add: Let_def)
  by fastforce

lemma mnn_distinct:
  assumes "invar k kdt" "dim p = k" "distinct ms" "set ms \<inter> set_kdt kdt = {}"
  shows "distinct (m_nearest_neighbors' m ms p kdt)"
  using assms
proof (induction kdt arbitrary: ms)
  case (Leaf p')
  thus ?case
    by (simp add: distinct_insort)
next
  case (Node a s l r)

  let ?cl = "m_nearest_neighbors' m ms p l"
  let ?cr = "m_nearest_neighbors' m ms p r"

  have "set ms \<inter> set_kdt l = {} \<and> set ms \<inter> set_kdt r = {}"
    using Node.prems(4) by auto
  hence DCLR: "distinct ?cl \<and> distinct ?cr"
    using Node.IH(1,2) Node.prems(1,2,3) invar_l invar_r by blast

  have "set ?cl \<inter> set_kdt r = {} \<and> set ?cr \<inter> set_kdt l = {}"
    using Node.prems(1,4) mnn_set invar_distinct by fastforce
  hence "distinct (m_nearest_neighbors' m ?cl p r) \<and> distinct (m_nearest_neighbors' m ?cr p l)"
    using Node.IH(1,2) Node.prems(1,2) DCLR invar_l invar_r by blast

  thus ?case 
    using DCLR by (auto simp add: Let_def)
qed




text\<open>Last auxiliary lemma and the main theorem.\<close>

lemma mnn_le_last_ms:
  assumes "invar k kdt" "dim p = k" "sqed_sorted p ms" "m \<le> length ms" "0 < m"
  shows "sqed (last (m_nearest_neighbors' m ms p kdt)) p \<le> sqed (last ms) p"
  using assms
proof (induction kdt arbitrary: ms)
  case (Leaf p')

  let ?ms' = "take m (sqed_insort p p' ms)"

  have "sqed_sorted p ?ms'"
    using Leaf.prems(3) sqed_sorted_take_insort by simp
  hence "\<forall>n \<in> set ?ms'. sqed n p \<le> sqed (last ?ms') p"
    using sqed_sorted_last by blast
  hence "\<forall>n \<in> set ?ms'. sqed n p \<le> sqed (last ms) p"
    using Leaf.prems(3,4,5)  by (smt sqed_sorted_last_take_insort_mono)
  thus ?case
    using Leaf.prems(5) by simp
next
  case (Node a s l r)

  let ?cl = "m_nearest_neighbors' m ms p l"
  let ?cr = "m_nearest_neighbors' m ms p r"

  have "m \<le> length ?cl"
    using mnn_length Node.prems(4) by auto
  hence "sqed (last (m_nearest_neighbors' m ?cl p r)) p \<le> sqed (last ?cl) p"
    using mnn_sorted Node.IH(2) Node.prems(1,2,3,5) invar_r by blast
  hence IHLR: "sqed (last (m_nearest_neighbors' m ?cl p r)) p \<le> sqed (last ms) p"
    using Node.IH(1) Node.prems invar_l mnn_length_gt_0 by smt

  have "m \<le> length ?cr"
    using mnn_length Node.prems(4) by auto
  hence "sqed (last (m_nearest_neighbors' m ?cr p l)) p \<le> sqed (last ?cr) p"
    using mnn_sorted Node.IH(1) Node.prems(1,2,3,5) invar_l by blast
  hence IHRL: "sqed (last (m_nearest_neighbors' m ?cr p l)) p \<le> sqed (last ms) p"
    using Node.IH(2) Node.prems invar_r mnn_length_gt_0 by smt

  show ?case 
    using Node IHLR IHRL by (auto simp add: Let_def)
qed

theorem mnn_sqed:
  assumes "invar k kdt" "dim p = k"
  assumes "sqed_sorted p ms" "set ms \<inter> set_kdt kdt = {}" "distinct ms" "0 < m"
  shows "\<forall>q \<in> set_kdt kdt \<union> set ms - set (m_nearest_neighbors' m ms p kdt). sqed (last (m_nearest_neighbors' m ms p kdt)) p \<le> sqed q p"
  using assms
proof (induction kdt arbitrary: ms)
  case (Leaf p')
  thus ?case
    using sqed_sorted_take_insort_mono by simp
next
  case (Node a s l r)

  let ?cl = "m_nearest_neighbors' m ms p l"
  let ?cr = "m_nearest_neighbors' m ms p r"

  have IHL: "\<forall>q \<in> set_kdt l \<union> set ms - set ?cl. sqed (last ?cl) p \<le> sqed q p"
    using Node.IH(1) Node.prems invar_l invar_set by blast
  have IHR: "\<forall>q \<in> set_kdt r \<union> set ms - set ?cr. sqed (last ?cr) p \<le> sqed q p"
    using Node.IH(2) Node.prems invar_r invar_set by blast

  have SORTED_L: "sqed_sorted p ?cl"
    using mnn_sorted Node.prems(3) by blast
  have SORTED_R: "sqed_sorted p ?cr"
    using mnn_sorted Node.prems(3) by blast

  have DISTINCT_L: "distinct ?cl"
    using Node.prems(1,2,4,5) mnn_distinct invar_set invar_l by blast
  have DISTINCT_R: "distinct ?cr"
    using Node.prems(1,2,4,5) mnn_distinct invar_set invar_r by blast

  consider (A) "p!a \<le> s \<and> length ?cl = m \<and> sqed p (last ?cl) \<le> sqed' s (p!a)"
         | (B) "p!a \<le> s \<and> \<not>(length ?cl = m \<and> sqed p (last ?cl) \<le> sqed' s (p!a))"
         | (C) "s < p!a \<and> length ?cr = m \<and> sqed p (last ?cr) \<le> sqed' s (p!a)"
         | (D) "s < p!a \<and> \<not>(length ?cr = m \<and> sqed p (last ?cr) \<le> sqed' s (p!a))"
    by argo
  thus ?case
  proof cases
    case A
    hence "\<forall>q \<in> set_kdt r. sqed (last ?cl) p \<le> sqed q p"
      using Node.prems(1,2) cutoff_r sqed_com by metis
    thus ?thesis
      using IHL A by auto
  next
    case B

    let ?mnn = "m_nearest_neighbors' m ?cl p r"

    have "set ?cl \<subseteq> set_kdt l \<union> set ms \<and> set ms \<inter> set_kdt r = {}"
      using mnn_set Node.prems(1,4) by auto
    hence IHLR: "\<forall>q \<in> set_kdt r \<union> set ?cl - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using SORTED_L DISTINCT_L Node.IH(2) Node.prems(1,2,6) invar_r invar_distinct by blast

    have "\<forall>n \<in> set ms - set ?cl. sqed (last ?mnn) p \<le> sqed n p"
    proof standard
      fix n
      assume *: "n \<in> set ms - set ?cl"

      hence "length ?cl = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "sqed (last ?mnn) p \<le> sqed (last ?cl) p"
        using mnn_le_last_ms SORTED_L invar_r Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cl) p \<le> sqed n p"
        using IHL * by blast
      thus "sqed (last ?mnn) p \<le> sqed n p"
        using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt r \<union> set ms - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using IHLR by auto

    have "\<forall>q \<in> set_kdt l - set ?cl. sqed (last ?mnn) p \<le> sqed q p"
    proof standard
      fix q
      assume *: "q \<in> set_kdt l - set ?cl"

      hence "length ?cl = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "sqed (last ?mnn) p \<le> sqed (last ?cl) p"
        using mnn_le_last_ms SORTED_L invar_r Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cl) p \<le> sqed q p"
        using IHL * by blast
      thus "sqed (last ?mnn) p \<le> sqed q p"
        using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt l - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using IHLR by blast

    show ?thesis
      using B R L by auto
  next
    case C
    hence "\<forall>q \<in> set_kdt l. sqed (last ?cr) p \<le> sqed q p"
      using Node.prems(1,2) cutoff_l sqed_com by smt
    thus ?thesis
      using IHR C by auto
  next
    case D

    let ?mnn = "m_nearest_neighbors' m ?cr p l"

    have "set ?cr \<subseteq> set_kdt r \<union> set ms \<and> set ms \<inter> set_kdt l = {}"
      using mnn_set Node.prems(1,4) by auto
    hence IHRL: "\<forall>q \<in> set_kdt l \<union> set ?cr - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using SORTED_R DISTINCT_R Node.IH(1) Node.prems(1,2,6) invar_l invar_distinct by blast

    have "\<forall>n \<in> set ms - set ?cr. sqed (last ?mnn) p \<le> sqed n p"
    proof standard
      fix n
      assume *: "n \<in> set ms - set ?cr"

      hence "length ?cr = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "sqed (last ?mnn) p \<le> sqed (last ?cr) p"
        using mnn_le_last_ms SORTED_R invar_l Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cr) p \<le> sqed n p"
        using IHR * by blast
      thus "sqed (last ?mnn) p \<le> sqed n p"
        using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt l \<union> set ms - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using IHRL by auto

    have "\<forall>q \<in> set_kdt r - set ?cr. sqed (last ?mnn) p \<le> sqed q p"
    proof standard
      fix q
      assume *: "q \<in> set_kdt r - set ?cr"

      hence "length ?cr = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "sqed (last ?mnn) p \<le> sqed (last ?cr) p"
        using mnn_le_last_ms SORTED_R invar_l Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cr) p \<le> sqed q p"
        using IHR * by blast
      thus "sqed (last ?mnn) p \<le> sqed q p" 
        using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt r - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using IHRL by blast

    show ?thesis 
      using D R L by auto
  qed
qed




text\<open>Wrapping up.\<close>

definition m_nearest_neighbors :: "nat \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point list" where
  "m_nearest_neighbors m p kdt = m_nearest_neighbors' m [] p kdt"

theorem m_nearest_neighbors_length:
  "length (m_nearest_neighbors m p kdt) = min m (size_kdt kdt)"
  using mnn_length m_nearest_neighbors_def by simp

theorem m_nearest_neighbors_sorted:
  "sqed_sorted p (m_nearest_neighbors m p kdt)"
  using mnn_sorted m_nearest_neighbors_def by simp

theorem m_nearest_neighbors_set:
  "set (m_nearest_neighbors m p kdt) \<subseteq> set_kdt kdt"
  using mnn_set m_nearest_neighbors_def by fastforce

theorem m_nearest_neighbors_distinct:
  assumes "invar k kdt" "dim p = k"
  shows "distinct (m_nearest_neighbors m p kdt)"
  using assms mnn_distinct m_nearest_neighbors_def by simp

theorem m_nearest_neighbors:
  assumes "invar k kdt" "dim p = k" "m_nearest_neighbors m p kdt = mns"
  shows "\<forall>q \<in> (set_kdt kdt - set mns). \<forall>n \<in> set mns. sqed n p \<le> sqed q p"
proof (cases "0 < m")
  case True
  hence "\<forall>q \<in> set_kdt kdt - set mns. sqed (last mns) p \<le> sqed q p"
    using assms m_nearest_neighbors_def mnn_sqed by auto
  hence "\<forall>q \<in> set_kdt kdt - set mns. \<forall>n \<in> set mns. sqed n p \<le> sqed q p"
    by (smt assms m_nearest_neighbors_sorted sqed_sorted_last)
  thus ?thesis
    using m_nearest_neighbors_def by blast
next
  case False
  hence "m = 0"
    by simp
  thus ?thesis
    using assms(3) m_nearest_neighbors_def mnn_length_gt_eq_m by fastforce
qed

end