theory Balanced
imports
  Complex_Main "KDTree" "Median_Of_Medians_Selection.Median_Of_Medians_Selection"
begin



text \<open>
  Partitioning points by axis < = > to some value m.
\<close>

fun partition :: "axis \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point list * point list * point list" where
  "partition _ _ [] = ([], [], [])"
| "partition a m (p # ps) = (
    let (lt, eq, gt) = partition a m ps in
    if p!a < m then 
      (p # lt, eq, gt)
    else if p!a = m then 
      (lt, p # eq, gt)
    else 
      (lt, eq, p # gt)
  )"

lemma partition_length:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "length ps = length lt + length eq + length gt"
    and "length lt + length eq = length (filter (\<lambda>p. p!a \<le> m) ps)"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_set:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "set ps = set lt \<union> set eq \<union> set gt"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_filter:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "lt = filter (\<lambda>p. p!a < m) ps"
    and "eq = filter (\<lambda>p. p!a = m) ps"
    and "gt = filter (\<lambda>p. m < p!a) ps"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)




text \<open>
  Finding the median of points wrt axis a.
\<close>

definition find_median :: "axis \<Rightarrow> point list \<Rightarrow> real" where
  "find_median a ps = (
    let n = length ps div 2 in
    let ps' = map (\<lambda>p. p!a) ps in
    fast_select n ps'
  )"

lemma length_filter_sort:
  "length (filter P (sort xs)) = length (filter P xs)"
  by (simp add: filter_sort)

lemma sorted_length_filter_le_k:
  assumes "k < length xs" "sorted xs"
  shows "k < length (filter (\<lambda>x. x \<le> xs!k) xs)"
proof -
  have 1: "{i. i \<le> k} \<subseteq> {i. i < length xs \<and> xs!i \<le> xs!k}"
    using assms sorted_nth_mono by auto
  have 2: "finite {i. i < length xs \<and> xs!i \<le> xs!k}"
    by simp
  have "k < card {i. i \<le> k}"
    by simp
  also have "... \<le> card {i. i < length xs \<and> xs!i \<le> xs!k}"
    using 1 2 card_mono by blast
  also have "... = length (filter (\<lambda>x. x \<le> xs!k) xs)"
    using length_filter_conv_card[of "\<lambda>x. x \<le> xs!k" xs] by simp
  finally show ?thesis .
qed

lemma sorted_length_filter_lt_k:
  assumes "k < length xs" "sorted xs"
  shows "length (filter (\<lambda>x. x < xs!k) xs) \<le> k"
proof -
  have 1: "{i. i < length xs \<and> xs!i < xs!k} \<subseteq> {i. i < k}"
    using sorted_nth_mono assms(2) not_le by fastforce
  have "length (filter (\<lambda>x. x < xs!k) xs) = card {i. i < length xs \<and> xs!i < xs!k}"
    using length_filter_conv_card by blast
  also have "... \<le> card {i. i < k}"
    using 1 card_mono by blast
  also have "... = k"
    by simp
  finally show ?thesis .
qed

lemma length_filter_sort_le_k:
  assumes "k < length xs"
  shows "k < length (filter (\<lambda>x. x \<le> sort xs!k) xs)"
  using assms sorted_length_filter_le_k[of k "sort xs"] by (simp add: length_filter_sort)

lemma length_filter_sort_lt_k:
  assumes "k < length xs"
  shows "length (filter (\<lambda>x. x < sort xs!k) xs) \<le> k"
  using assms sorted_length_filter_lt_k[of k "sort xs"] by (simp add: length_filter_sort)

lemma length_filter_map_axis_lt: (* use length_filter_map ? *)
  "length (filter (\<lambda>a. a < k) (map (\<lambda>p. p!a) ps)) = length (filter (\<lambda>p. p!a < k) ps)"
  by (induction ps) auto

lemma length_filter_map_axis_le: (* use length_filter_map ? *)
  "length (filter (\<lambda>a. a \<le> k) (map (\<lambda>p. p!a) ps)) = length (filter (\<lambda>p. p!a \<le> k) ps)"
  by (induction ps) auto

lemma find_median_filter:
  assumes "length ps > 0"
  shows "length ps div 2 < length (filter (\<lambda>p. p!a \<le> find_median a ps) ps)"
    and "length (filter (\<lambda>p. p!a < find_median a ps) ps) \<le> length ps div 2"
proof -
  let ?n = "length ps div 2"
  let ?ps' = "map (\<lambda>p. p!a) ps"
  let ?m = "sort ?ps' ! ?n"
  let ?m' = "fast_select ?n ?ps'"

  have *: "?n < length ?ps'"
    using assms by auto

  have "?n < length (filter (\<lambda>a. a \<le> ?m) ?ps')"
    using * length_filter_sort_le_k[of ?n ?ps'] by blast
  hence "?n < length (filter (\<lambda>p. p!a \<le> ?m) ps)"
    using length_filter_map_axis_le[of ?m a] by simp
  hence 1: "?n < length (filter (\<lambda>p. p!a \<le> ?m') ps)"
    using * fast_select_correct[of ?n ?ps'] select_def[of ?n ?ps'] by force

  have "length (filter (\<lambda>a. a < ?m) ?ps') \<le> ?n"
    using * length_filter_sort_lt_k[of ?n ?ps'] by blast
  hence "length (filter (\<lambda>p. p!a < ?m) ps) \<le> ?n"
    using length_filter_map_axis_lt[of ?m a] by simp
  hence 2: "length (filter (\<lambda>p. p!a < ?m') ps) \<le> ?n"
    using * fast_select_correct[of ?n ?ps'] select_def[of ?n ?ps'] by force

  show "length ps div 2 < length (filter (\<lambda>p. p!a \<le> find_median a ps) ps)"
       "length (filter (\<lambda>p. p!a < find_median a ps) ps) \<le> length ps div 2"
    unfolding find_median_def using 1 2 by metis+
qed




text \<open>
  Partitioning point balanced wrt the median at axis a.
\<close>

definition partition_by_median :: "axis \<Rightarrow> point list \<Rightarrow> point list * real * point list" where
  "partition_by_median a ps = (
     let m = find_median a ps in
     let (lt, eq, gt) = partition a m ps in
     let rem = length ps div 2 - length lt in
     (lt @ take rem eq, m, drop rem eq @ gt)
  )"

lemma partition_by_median_set:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "set ps = set l \<union> set r"
  using assms unfolding partition_by_median_def
  apply (simp add: Let_def split: prod.splits)
  by (smt partition_set append_take_drop_id set_append inf_sup_aci(6))

lemma partition_by_median_filter:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "\<forall>p \<in> set l. p!a \<le> m"
    and "\<forall>p \<in> set r. m \<le> p!a"
  using assms unfolding partition_by_median_def
  apply (auto simp add: Let_def split: prod.splits)
  by (smt partition_filter in_set_takeD in_set_dropD mem_Collect_eq set_filter)+

lemma partition_by_median_length_1:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "length ps = length l + length r"
  using assms unfolding partition_by_median_def
  apply (simp add: Let_def min_def split: prod.splits)
  by (smt add.assoc partition_length)

lemma partition_by_median_length_2:
  assumes "(l, m, r) = partition_by_median a ps" "length ps > 0"
  shows "length r - length l \<le> 1"
    and "length r \<ge> length l"
proof -
  let ?n = "length ps div 2"
  let ?m = "find_median a ps"
  let ?leg = "partition a ?m ps"
  let ?lt = "fst ?leg"
  let ?eq = "fst (snd ?leg)"
  let ?gt = "snd (snd ?leg)"
  let ?rem = "?n - length ?lt"
  let ?l = "?lt @ take ?rem ?eq"
  let ?r = "drop ?rem ?eq @ ?gt"

  have "(?lt, ?eq, ?gt) = partition a ?m ps"
    by simp
  hence "?n < length ?lt + length ?eq" "length ?lt \<le> ?n"
    using assms(2) partition_length(2) partition_filter(1) find_median_filter by metis+
  hence 0: "length ?l = ?n"
    by simp

  have 1: "(?l, ?m, ?r) = partition_by_median a ps"
    by (auto simp add: Let_def partition_by_median_def split: prod.splits)
  hence 2: "length ps = length ?l + length ?r"
    using assms partition_by_median_length_1 by blast

  have 3: "length ?l \<le> length ?r"
    using 0 2 by linarith

  hence "?n \<le> length ?r"
    using 0 by linarith
  hence 4: "length ?r - length ?l \<le> 1"
    using 0 2 by linarith

  show "length r - length l \<le> 1"
       "length r \<ge> length l" using 1 3 4
    by (metis Pair_inject assms(1))+
qed

lemma partition_by_median_length_3: 
  assumes "(l, m, r) = partition_by_median a ps" "0 < length ps"
  shows "length l < length ps"
proof (rule ccontr)
  assume *: "\<not> (length l < length ps)"
  have "length ps = length l + length r"
    using partition_by_median_length_1 assms(1) by simp
  hence "length l = length ps" "length r = 0"
    using * by simp_all
  moreover have "length l \<le> length r"
    using partition_by_median_length_2 assms by fastforce+
  ultimately show "False" using assms(2) by simp
qed

lemma partition_by_median_length_4: 
  assumes "(l, m, r) = partition_by_median a ps" "1 < length ps"
  shows "length r < length ps"
proof (rule ccontr)
  assume *: "\<not> (length r < length ps)"
  have "length ps = length l + length r"
    using partition_by_median_length_1 assms(1) by simp
  hence "length r = length ps" "length l = 0"
    using * by simp_all
  moreover have "length r - length l \<le> 1"
    using partition_by_median_length_2 assms by fastforce+
  ultimately show "False" using assms(2) by simp
qed

lemma partition_by_median_length_5:
  assumes "(l, m, r) = partition_by_median a ps" "1 < length ps"
  shows "0 < length l"
    and "0 < length r"
  using assms partition_by_median_length_1 partition_by_median_length_4 apply simp
  using assms partition_by_median_length_1 partition_by_median_length_3 by fastforce

lemmas partition_by_median_length = 
  partition_by_median_length_1 partition_by_median_length_2
  partition_by_median_length_3 partition_by_median_length_4
  partition_by_median_length_5




function (sequential) build' :: "axis \<Rightarrow> dimension \<Rightarrow> point list \<Rightarrow> kdt" where
  "build' a d [] = undefined"
| "build' a d [p] = Leaf p" 
| "build' a d ps = (
    let a' = (a + 1) mod d in
    let (l, m, r) = partition_by_median a ps in
    Node a m (build' a' d l) (build' a' d r)
  )"
  by pat_completeness auto
termination build'
  using partition_by_median_length(4,5)
  apply (relation "measure (\<lambda>(a, d, ps). length ps)")
  apply (auto)
  apply fastforce+
  done

lemma build'_simp_1:
  "ps = [p] \<Longrightarrow> build' a d ps = Leaf p"
  by simp

lemma build'_simp_2:
  "ps = p\<^sub>0 # p\<^sub>1 # ps' \<Longrightarrow> a' = (a + 1) mod d \<Longrightarrow> (l, m, r) = partition_by_median a ps \<Longrightarrow> build' a d ps = Node a m (build' a' d l) (build' a' d r)"
  using build'.simps(3) by (auto simp add: Let_def split: prod.splits)

lemma length_ps_gt_1:
  "length ps > 1 \<Longrightarrow> \<exists>p\<^sub>0 p\<^sub>1 ps'. ps = p\<^sub>0 # p\<^sub>1 # ps'"
  by (induction ps) (auto simp add: neq_Nil_conv)

lemma build'_simp_3:
  "length ps > 1 \<Longrightarrow> a' = (a + 1) mod d \<Longrightarrow> (l, m, r) = partition_by_median a ps \<Longrightarrow> build' a d ps = Node a m (build' a' d l) (build' a' d r)"
  using build'_simp_2 length_ps_gt_1 by fast

lemmas build'_simps[simp] = build'_simp_1 build'_simp_2 build'_simp_3

declare build'.simps[simp del]




lemma build'_set:
  assumes "0 < length ps"
  shows "set ps = set_kdt (build' a d ps)"
  using assms
proof (induction ps arbitrary: a rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have "set ?l = set_kdt (build' ?a' d ?l)" "set ?r = set_kdt (build' ?a' d ?r)" 
      using False partition_by_median_length(4,5,6,7)[of ?l ?m ?r a ps] "1.IH" by force+
    moreover have "set ps = set ?l \<union> set ?r"
      using partition_by_median_set by (metis prod.collapse)
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis by auto
  qed
qed

lemma build'_invar:
  assumes "0 < length ps" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "a < d"
  shows "invar d (build' a d ps)"
  using assms
proof (induction ps arbitrary: a rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where P: "ps = [p]"
      using "1.prems" by (cases ps) auto
    hence "dim p = d"
      using "1.prems"(2) by simp
    thus ?thesis using P by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have A': "?a' < d"
      using "1.prems"(4) by auto

    have *: "length ps = length ?l + length ?r"
      using partition_by_median_length by (metis prod.collapse)+
    hence **: "length ?l < length ps" "length ?r < length ps"
      using False partition_by_median_length(4,5) not_le_imp_less "1.prems" by (smt prod.collapse)+
    hence ***: "0 < length ?l" "0 < length ?r"
      using * False partition_by_median_length(6,7) by simp_all
    moreover have SPLR: "set ps = set ?l \<union> set ?r"
      using partition_by_median_set by (metis prod.collapse)
    moreover have "distinct ?l" "distinct ?r" and LR: "set ?l \<inter> set ?r = {}"
      using "1.prems"(3) SPLR * by (metis card_distinct distinct_append distinct_card length_append set_append)+
    moreover have "\<forall>p \<in> set ?l .dim p = d" "\<forall>p \<in> set ?r .dim p = d"
      using "1.prems"(2) SPLR by simp_all
    ultimately have "invar d (build' ?a' d ?l)" "invar d (build' ?a' d ?r)"
      using "1.IH" A' ** by simp_all
    moreover have "\<forall>p \<in> set ?l. p ! a \<le> ?m" "\<forall>p \<in> set ?r. ?m \<le> p ! a"
      using partition_by_median_filter by (metis prod.collapse)+
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis using "1.prems"(4) LR *** build'_set by auto
  qed
qed

lemma build'_size:
  assumes "length ps > 0"
  shows "size (build' a d ps) = length ps"
  using assms
proof (induction ps arbitrary: a rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 2: "length ps = length ?l + length ?r" "length ?r - length ?l \<le> 1" "length ?l \<le> length ?r"
      using "1.prems" partition_by_median_length by (metis prod.collapse)+
    moreover have "length ?l < length ps" "length ?r < length ps"
      using False "1.prems" 2 by auto
    ultimately have "size (build' ?a' d ?l) = length ?l" "size (build' ?a' d ?r) = length ?r" 
      using "1.IH" by simp_all
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis using 2 by simp
  qed
qed

lemma AUX:
  fixes r :: nat and l :: nat
  assumes "r - l \<le> 1" "r \<ge> l"
  shows "l + 1 = r \<or> l = r"
  using assms by linarith

lemma build'_balanced:
  assumes "length ps > 0"
  shows "balanced (build' a d ps)"
  using assms
proof (induction ps arbitrary: a rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis unfolding balanced_def by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 2: "length ps = length ?l + length ?r" "length ?r - length ?l \<le> 1" "length ?l \<le> length ?r"
      using partition_by_median_length(1,2,3) "1.prems" by (metis prod.collapse)+
    hence 3: "length ?l + 1 = length ?r \<or> length ?l = length ?r"
      using AUX by simp
    moreover have 4: "length ?l < length ps" "length ?r < length ps"
      using False 2(1,2,3) by auto
    moreover have 5: "length ?l > 0" "length ?r > 0"
      using "1.prems" "2"(1) 3 4 by linarith+
    ultimately have B: "balanced (build' ?a' d ?l)" "balanced (build' ?a' d ?r)"
      using "1.IH" by simp_all

    have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    moreover have "size (build' ?a' d ?l) + 1 = size (build' ?a' d ?r) \<or> size (build' ?a' d ?l) = size (build' ?a' d ?r)"
      using 3 5 build'_size by simp
    ultimately show ?thesis using B balanced_Node_if_wbal2 by auto
  qed
qed

lemma complete_if_balanced_size_2powh:
  assumes "balanced kdt" "size kdt = 2 ^ h"
  shows "complete kdt"
proof (rule ccontr)
  assume "\<not> complete kdt"
  hence "2 ^ (min_height kdt) < size kdt" "size kdt < 2 ^ height kdt"
    by (simp_all add: min_height_size_if_incomplete size_height_if_incomplete)
  hence "height kdt - min_height kdt > 1"
    using assms(2) by simp
  hence "\<not> balanced kdt"
    using balanced_def by simp
  thus "False"
    using assms(1) by simp
qed

lemma build'_complete:
  assumes "length ps = 2 ^ k"
  shows "complete (build' a d ps)"
  using assms complete_if_balanced_size_2powh
  by (simp add: build'_balanced build'_size)




definition build :: "point list \<Rightarrow> kdt" where
  "build ps = build' 0 (dim (hd ps)) ps"

theorem build_set:
  "0 < length ps \<Longrightarrow> set ps = set_kdt (build ps)"
  using build'_set build_def by simp

theorem build_invar:
  "0 < length ps  \<Longrightarrow> \<forall>p \<in> set ps. dim p = d \<Longrightarrow> distinct ps \<Longrightarrow> 0 < d \<Longrightarrow> invar d (build ps)"
  using build'_invar build_def by simp

theorem build_size:
  "0 < length ps \<Longrightarrow> length ps = size (build ps)"
  using build'_size build_def by simp

theorem build_balanced:
  "0 < length ps \<Longrightarrow> balanced (build ps)"
  using build'_balanced build_def by simp

theorem build_complete:
  "length ps = 2 ^ k \<Longrightarrow> complete (build ps)"
  using build'_complete build_def by simp

theorem build_height:
  "length ps = 2 ^ k \<Longrightarrow> length ps = 2 ^ (height (build ps))"
  using build_complete build_size complete_iff_size by auto

end