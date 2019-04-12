theory Spread
  imports Complex_Main KDTree
begin

type_synonym spread = real

fun spread :: "real \<Rightarrow> axis \<Rightarrow> point list \<Rightarrow> (real * real)" where
  "spread d a [] = (d, d)"
| "spread d a (p#ps) = (
    let (l, h) = spread d a ps in
    (min (p!a) l, max (p!a) h)
  )"

lemma spread:
  "\<forall>x \<in> set (map (\<lambda>p. p!a) ps) \<union> {d}. fst (spread d a ps) \<le> x"
  apply (induction ps)
  apply (auto split: prod.splits)
  done

lemma
  "fst (spread d a ps) \<in> set (map (\<lambda>p. p!a) ps) \<union> {d}"
  apply (induction ps)
   apply (auto simp add: min_def split: prod.splits)
  done

end