theory hw_orginal_1
imports
  Complex_Main
begin

text \<open> 
  Type synonyms and definitions
\<close>

type_synonym point = "real list"
type_synonym axis = nat
type_synonym dimension = nat
type_synonym split = real

datatype kdt =
  Leaf point
| Node kdt split kdt

definition dim :: "point \<Rightarrow> nat"  where
  "dim p = length p"

definition incr :: "axis \<Rightarrow> dimension \<Rightarrow> axis" where
  "incr a d = (a + 1) mod d"

declare dim_def[simp]
declare incr_def[simp]




text \<open> 
  Invariant and abstraction function
\<close>

fun set_kdt :: "kdt \<Rightarrow> point set" where
  "set_kdt (Leaf p) = {p}"
| "set_kdt (Node l _ r) = set_kdt l \<union> set_kdt r"

fun invar' :: "axis \<Rightarrow> dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar' _ k (Leaf p) \<longleftrightarrow> k > 0 \<and> dim p = k"
| "invar' a k (Node l s r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. p!a \<le> s) \<and> (\<forall>p \<in> set_kdt r. p!a > s) \<and>
    invar' (incr a k) k l \<and> invar' (incr a k) k r"

lemma invar'_l:
  assumes "invar' a k (Node l s r)"
  shows "invar' (incr a k) k l"
  using assms by simp

lemma invar'_r:
  assumes "invar' a k (Node l s r)"
  shows "invar' (incr a k) k r"
  using assms by simp

lemma invar'_dim_gt_0:
  assumes "invar' a k kdt"
  shows "k > 0"
  using assms by (induction kdt arbitrary: a) auto
  
lemma invar'_dim:
  assumes "invar' a k kdt"
  shows "\<forall>p \<in> set_kdt kdt. dim p = k"
  using assms by (induction kdt arbitrary: a) auto

lemma invar'_l_le_a: 
  assumes "invar' a k kdt" "kdt = Node l s r"
  shows "\<forall>p \<in> set_kdt l. p!a \<le> s"
  using assms invar'.simps(2) by blast

lemma invar'_r_gt_a: 
  assumes "invar' a k kdt" "kdt = Node l s r"
  shows "\<forall>p \<in> set_kdt r. s < p!a"
  using assms invar'.simps(2) by blast




text \<open>
  Definitions for the euclidean distance.
  Squared euclidean distance to avoid roots.
\<close>

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
  "sqed' x y \<ge> 0"
  using sqed'_def by simp

lemma sqed'_eq_0[simp]:
  "sqed' x y = 0 \<longleftrightarrow> x = y"
  using sqed'_def by simp

lemma sqed'_com:
  "sqed' x y = sqed' y x"
  using sqed'_def by (simp add: power2_commute)

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
  assumes "x \<le> s" "s \<le> y"
  shows "sqed' x y \<ge> sqed' x s + sqed' s y"
  unfolding sqed'_def using inequality assms by smt

lemma sqed_ge_0:
  assumes "dim p\<^sub>0 = dim p\<^sub>1"
  shows "sqed p\<^sub>0 p\<^sub>1 \<ge> 0"
  using assms by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_ge_0)

lemma sqed_eq_0[simp]:
  assumes "p\<^sub>0 = p\<^sub>1"
  shows "sqed p\<^sub>0 p\<^sub>1 = 0"
  using assms by(induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) auto

lemma sqed_com:
  assumes "dim p\<^sub>0 = dim p\<^sub>1"
  shows "sqed p\<^sub>0 p\<^sub>1 = sqed p\<^sub>1 p\<^sub>0"
  using assms by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_com)




text\<open>
  The nearest neighbor algorithm.
\<close>

fun nearest_neighbor' :: "axis \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point" where
  "nearest_neighbor' _ _ _ (Leaf p) = p"
| "nearest_neighbor' a k p (Node l s r) = (
    if p!a \<le> s then
      let candidate = nearest_neighbor' (incr a k) k p l in
      if sqed p candidate \<le> sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor' (incr a k) k p r in
        min_by_sqed candidate candidate' p
    else
      let candidate = nearest_neighbor' (incr a k) k p r in
      if sqed p candidate < sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor' (incr a k) k p l in
        min_by_sqed candidate candidate' p
  )"

text \<open>
  Warmup
\<close>

lemma nearest_neighbor'_in_kdt:
  assumes "invar' a k kdt" "dim p = k"
  shows "nearest_neighbor' a k p kdt \<in> set_kdt kdt"
  using assms by (induction kdt arbitrary: a) (auto simp add: Let_def min_by_sqed_def)

text \<open>
  Auxiliary lemmas for main proof
\<close>

lemma minimize_sqed:
  assumes "dim p\<^sub>0 = k" "dim p\<^sub>1 = k" "a < k"
  shows "sqed p\<^sub>0 p\<^sub>1 \<ge> sqed' (p\<^sub>0!a) (p\<^sub>0[a := (p\<^sub>1!a)]!a)"
  using assms
  apply (induction p\<^sub>0 p\<^sub>1 arbitrary: a k rule: sqed.induct)
  apply (auto simp add: sqed_ge_0 split: nat.splits)
  by (smt sqed'_ge_0)

lemma cutoff_r:
  assumes "invar' a k (Node l s r)" "p!a \<le> s" "c \<in> set_kdt l" "dim p = k" "a < k" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt r. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume A: "q \<in> set_kdt r"

  let ?q' = "p[a := (q!a)]"

  have "sqed p q \<ge> sqed' (p!a) (?q'!a)"
    using A minimize_sqed assms(1,4,5) invar'_dim invar'_r by blast
  hence "sqed p q \<ge> sqed' (p!a) s + sqed' s (q!a)"
    by (smt A assms(1,2,4,5) dim_def nth_list_update_eq invar'_r_gt_a sqed'_split)
  hence "sqed p q \<ge> sqed p c"
    by (smt assms(6) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed

lemma cutoff_l:
  assumes "invar' a k (Node l s r)" "p!a > s" "c \<in> set_kdt r" "dim p = k" "a < k" "sqed p c < sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt l. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume A: "q \<in> set_kdt l"

  let ?q' = "p[a := (q!a)]"

  have "sqed p q \<ge> sqed' (p!a) (?q'!a)"
    using A minimize_sqed assms(1,4,5) invar'_dim invar'_l by blast
  hence "sqed p q \<ge> sqed' (p!a) s + sqed' s (q!a)"
    by (smt A assms(1,2,4,5) dim_def invar'_l_le_a nth_list_update_eq sqed'_com sqed'_split)
  hence "sqed p q \<ge> sqed p c"
    by (smt assms(6) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed

text \<open>
  Main proof
\<close>

lemma nearest_neighbor'_minimal:
  assumes "invar' a k kdt" "dim p = k" "a < k"
  shows "\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor' a k p kdt) p \<le> sqed q p"
  using assms
proof (induction kdt arbitrary: a)
  case (Leaf p)
  thus ?case by simp                                      
next
  case (Node l s r)
  let ?candidate_l = "nearest_neighbor' (incr a k) k p l"
  let ?candidate_r = "nearest_neighbor' (incr a k) k p r"

  have IHL: "\<forall>q \<in> set_kdt l. sqed ?candidate_l p \<le> sqed q p"
    using Node.IH(1) Node.prems(1,3) assms(2) by auto
  have IHR: "\<forall>q \<in> set_kdt r. sqed ?candidate_r p \<le> sqed q p"
    using Node.IH(2) Node.prems(1,3) assms(2) by auto
 
  have CUTOFF_L: "s < p!a \<longrightarrow> sqed p ?candidate_r < sqed' s (p!a) \<longrightarrow> (\<forall>q \<in> set_kdt l. sqed p ?candidate_r \<le> sqed p q)"
    using Node.prems(1,3) assms(2) cutoff_l invar'_r nearest_neighbor'_in_kdt by blast
  have CUTOFF_R: "p!a \<le> s \<longrightarrow> sqed p ?candidate_l \<le> sqed' s (p!a) \<longrightarrow> (\<forall>q \<in> set_kdt r. sqed p ?candidate_l \<le> sqed p q)"
    using Node.prems(1,3) assms(2) cutoff_r invar'_l nearest_neighbor'_in_kdt by blast

  have LY: "p!a \<le> s \<longrightarrow> sqed p ?candidate_l \<le> sqed' s (p!a) \<longrightarrow> ?case"
    using Node.prems IHL CUTOFF_R apply (auto) by (metis assms(2) invar'_dim nearest_neighbor'_in_kdt sqed_com)
  have LN: "p!a \<le> s \<longrightarrow> \<not>sqed p ?candidate_l \<le> sqed' s (p!a) \<longrightarrow> ?case"
    using Node.prems IHL IHR by (auto simp add: min_by_sqed_def Let_def)

  have RY: "s < p!a \<longrightarrow> sqed p ?candidate_r < sqed' s (p!a) \<longrightarrow> ?case"
    using Node.prems IHR CUTOFF_L apply (auto) by (metis (mono_tags, lifting) assms(2) invar'_dim nearest_neighbor'_in_kdt sqed_com)
  have RN: "s < p!a \<longrightarrow> \<not>sqed p ?candidate_r < sqed' s (p!a) \<longrightarrow> ?case"
    using Node.prems IHL IHR by (auto simp add: min_by_sqed_def Let_def)

  show ?case using LY LN RY RN by argo
qed

theorem nearest_neighbor':
  assumes "invar' a k kdt" "dim p = k" "a < k"
  shows "(\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor' a k p kdt) p \<le> sqed q p) \<and> nearest_neighbor' a k p kdt \<in> set_kdt kdt"
  using assms nearest_neighbor'_in_kdt nearest_neighbor'_minimal by simp

text \<open>
  I would like to drop explicitly passing the splitting axis into every function.
  Define abbreviations and start splitting at 0th axis.
\<close>

abbreviation invar where
  "invar \<equiv> invar' 0"

definition nearest_neighbor :: "point \<Rightarrow> kdt \<Rightarrow> point" where
  "nearest_neighbor p = nearest_neighbor' 0 (dim p) p"

lemma nearest_neighbor_in_kdt:
  assumes "invar k kdt" "dim p = k"
  shows "nearest_neighbor p kdt \<in> set_kdt kdt"
  using assms by (simp add: nearest_neighbor'_in_kdt nearest_neighbor_def)

lemma nearest_neighbor_minimal:
  assumes "invar k kdt" "dim p = k"
  shows "\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor p kdt) p \<le> sqed q p"
  using assms by (simp add: invar'_dim_gt_0 nearest_neighbor'_minimal nearest_neighbor_def)

theorem nearest_neighbor:
  assumes "invar k kdt" "dim p = k"
  shows "(\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor p kdt) p \<le> sqed q p) \<and> nearest_neighbor p kdt \<in> set_kdt kdt"
  using assms nearest_neighbor_in_kdt nearest_neighbor_minimal by simp

(* *** *)
fun partition :: "axis \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> (point list * point list)" where
  "partition _ _ [] = ([], [])"
| "partition a p (x # xs) = (
    let (as, bs) = partition a p xs in
    if x!a \<le> p!a then
      (x # as, bs)
    else
      (as, x # bs)
  )"

fun select :: "axis \<Rightarrow> point list \<Rightarrow> nat \<Rightarrow> point" where
  "select _ [] _ = undefined"
| "select _ [p] _ = p"
| "select a (p # ps) k = (
    let (lps, hps) = partition a p ps in
    if k = length ps then
      p
    else if k < length ps then
      select a lps k
    else
      select a hps (k - length ps)
  )"
termination
  apply size_change
  done

lemma partition_left_lt_or_eq:
  "\<forall>p' \<in> set (fst (partition a p ps)). p'!a \<le> p!a"
  by (induction ps) (auto split: prod.splits)

lemma partition_right_gt:
  "\<forall>p' \<in> set (snd (partition a p ps)). p'!a > p!a"
  by (induction ps) (auto split: prod.splits)

lemma partition_length:
  "length ps = length (fst (partition a p ps)) + length (snd (partition a p ps))"
  by (induction ps) (auto split: prod.splits)

lemma partition:
  "set ps = set (fst (partition a p ps)) \<union> set (snd (partition a p ps))"
proof standard
  show "set ps \<subseteq> set (fst (partition a p ps)) \<union> set (snd (partition a p ps))"
    by (induction ps) (auto split: prod.splits)
next
  show "set ps \<supseteq> set (fst (partition a p ps)) \<union> set (snd (partition a p ps))"
  by (induction ps) (auto split: prod.splits)
qed

end