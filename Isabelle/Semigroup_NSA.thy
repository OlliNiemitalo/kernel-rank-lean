theory Semigroup_NSA
  imports
    "HOL-Analysis.Analysis"
    "HOL-Nonstandard_Analysis.Nonstandard_Analysis"
begin

no_notation eqpoll (infixl \<open>\<approx>\<close> 50)

text \<open>
  A nonstandard proof, after Euler, that a one-parameter semigroup \<open>M\<close> that is continuous on
  \<open>[0, \<infinity>)\<close> is an exponential, \<open>M t = exp (t A)\<close>, in a finite-dimensional
  (Heine--Borel) Banach algebra.

  \<^enum> The difference quotients \<open>(M h - 1) / h\<close> along \<open>h = \<delta> / n\<close> are bounded
    (geometric sums; ordinary analysis).
  \<^enum> By transfer, \<open>(M \<eta> - 1) / \<eta>\<close> is finite for the infinitesimal
    \<open>\<eta> = \<delta> / \<omega>\<close>, so it has a standard part \<open>A\<close>.
  \<^enum> Each step of size \<open>\<eta>\<close> multiplies \<open>M s * exp (- s A)\<close> by a factor
    that differs from \<open>1\<close> by \<open>\<eta>\<close> times an infinitesimal. Over
    \<open>\<lfloor>t / \<eta>\<rfloor>\<close> steps the changes add up to an infinitesimal
    (a transferred telescoping estimate), so the product stays \<open>1\<close>.
\<close>

section \<open>Ordinary analysis: bounded difference quotients and telescoping\<close>

lemma semigroup_pow:
  fixes M :: "real \<Rightarrow> 'a::monoid_mult"
  assumes M0: "M 0 = 1"
    and add: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
    and "0 \<le> h"
  shows "M (real n * h) = M h ^ n"
proof (induction n)
  case 0
  then show ?case using M0 by simp
next
  case (Suc n)
  have "0 \<le> real n * h" using \<open>0 \<le> h\<close> by simp
  then have "M (real (Suc n) * h) = M (real n * h) * M h"
    using add[of "real n * h" h] \<open>0 \<le> h\<close> by (simp add: algebra_simps)
  then show ?case using Suc by (simp add: power_commutes)
qed

lemma geom_telescope:
  fixes x :: "'a::ring_1"
  shows "(x - 1) * (\<Sum>i<n. x ^ i) = x ^ n - 1"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(x - 1) * (\<Sum>i<Suc n. x ^ i) = (x - 1) * (\<Sum>i<n. x ^ i) + (x - 1) * x ^ n"
    by (simp add: distrib_left)
  also have "\<dots> = (x ^ n - 1) + (x - 1) * x ^ n"
    by (simp only: Suc.IH)
  also have "\<dots> = x ^ Suc n - 1"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma geometric_quotient_bound:
  fixes x :: "'a::real_normed_algebra_1"
  assumes "0 < n" and near: "\<And>k. k < n \<Longrightarrow> norm (x ^ k - 1) \<le> 1 / 2"
  shows "norm (real n *\<^sub>R (x - 1)) \<le> 2 * norm (x ^ n - 1)"
proof -
  define S where "S = (\<Sum>k<n. x ^ k)"
  define q where "q = (1 / real n) *\<^sub>R S"
  define d where "d = real n *\<^sub>R (x - 1)"
  have "d * q = (x - 1) * S"
    using \<open>0 < n\<close> by (simp add: d_def q_def)
  then have dq: "d * q = x ^ n - 1"
    by (simp add: S_def geom_telescope)
  have sum1: "(\<Sum>k<n. (1 - x ^ k)) = real n *\<^sub>R 1 - S"
    by (simp add: S_def sum_subtractf scaleR_conv_of_real)
  have "1 - q = (1 / real n) *\<^sub>R (\<Sum>k<n. (1 - x ^ k))"
    using \<open>0 < n\<close> by (simp add: sum1 q_def scaleR_diff_right)
  then have "norm (1 - q) = (1 / real n) * norm (\<Sum>k<n. (1 - x ^ k))"
    by simp
  also have "\<dots> \<le> (1 / real n) * (\<Sum>k<n. norm (1 - x ^ k))"
    by (intro mult_left_mono norm_sum) simp
  also have "\<dots> \<le> (1 / real n) * (\<Sum>k<n. 1 / 2)"
    using near by (intro mult_left_mono sum_mono) (simp_all add: norm_minus_commute)
  also have "\<dots> = 1 / 2"
    using \<open>0 < n\<close> by simp
  finally have hq: "norm (1 - q) \<le> 1 / 2" .
  have "d = d * q + d * (1 - q)"
    by (simp add: algebra_simps)
  then have "norm d \<le> norm (d * q) + norm (d * (1 - q))"
    by (metis norm_triangle_ineq)
  moreover have "norm (d * (1 - q)) \<le> norm d * norm (1 - q)"
    by (rule norm_mult_ineq)
  moreover have "norm d * norm (1 - q) \<le> norm d * (1 / 2)"
    using hq by (intro mult_left_mono) simp_all
  ultimately have "norm d \<le> norm (x ^ n - 1) + norm d * (1 / 2)"
    unfolding dq[symmetric] by linarith
  then show ?thesis
    by (simp add: d_def)
qed

lemma exists_bounded_quotients:
  fixes M :: "real \<Rightarrow> 'a::real_normed_algebra_1"
  assumes cont: "continuous (at 0 within {0..}) M" and M0: "M 0 = 1"
    and add: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
  shows "\<exists>\<delta>>0. \<exists>C. \<forall>n.
    norm ((1 / (\<delta> / real (Suc n))) *\<^sub>R (M (\<delta> / real (Suc n)) - 1)) \<le> C"
proof -
  have "(M \<longlongrightarrow> 1) (at 0 within {0..})"
    using cont M0 by (simp add: continuous_within)
  then have "\<forall>\<^sub>F s in at 0 within {0..}. dist (M s) 1 < 1 / 2"
    by (rule tendstoD) simp
  then obtain r where "r > 0"
    and r: "\<And>s. s \<in> {0..} \<Longrightarrow> s \<noteq> 0 \<Longrightarrow> dist s 0 < r \<Longrightarrow> dist (M s) 1 < 1 / 2"
    unfolding eventually_at by blast
  define \<delta> where "\<delta> = r / 2"
  have "\<delta> > 0" using \<open>r > 0\<close> by (simp add: \<delta>_def)
  have near: "norm (M s - 1) \<le> 1 / 2" if "0 \<le> s" "s \<le> \<delta>" for s
  proof (cases "s = 0")
    case True
    then show ?thesis using M0 by simp
  next
    case False
    then have "dist (M s) 1 < 1 / 2"
      using r[of s] that \<open>r > 0\<close> by (simp add: \<delta>_def)
    then show ?thesis by (simp add: dist_norm)
  qed
  have bound: "norm ((1 / (\<delta> / real (Suc n))) *\<^sub>R (M (\<delta> / real (Suc n)) - 1))
      \<le> 2 * norm (M \<delta> - 1) / \<delta>" for n
  proof -
    define m where "m = Suc n"
    define h where "h = \<delta> / real m"
    have "0 < h" using \<open>\<delta> > 0\<close> by (simp add: h_def m_def)
    have mh: "real m * h = \<delta>" by (simp add: h_def m_def)
    have pow: "M h ^ k = M (real k * h)" for k
      using semigroup_pow[of M h k, OF M0 add] \<open>0 < h\<close> by simp
    have steps: "norm (M h ^ k - 1) \<le> 1 / 2" if "k < m" for k
    proof -
      have "real k * h \<le> real m * h"
        using that \<open>0 < h\<close> by (intro mult_right_mono) simp_all
      then show ?thesis
        unfolding pow using \<open>0 < h\<close> mh by (intro near) simp_all
    qed
    have "norm (real m *\<^sub>R (M h - 1)) \<le> 2 * norm (M h ^ m - 1)"
      by (rule geometric_quotient_bound[OF _ steps]) (simp add: m_def)
    then have "norm (real m *\<^sub>R (M h - 1)) \<le> 2 * norm (M \<delta> - 1)"
      by (simp add: pow mh)
    moreover have "norm ((1 / h) *\<^sub>R (M h - 1)) = norm (real m *\<^sub>R (M h - 1)) / \<delta>"
      using \<open>\<delta> > 0\<close> by (simp add: h_def m_def)
    ultimately show ?thesis
      using \<open>\<delta> > 0\<close> by (simp add: h_def m_def divide_right_mono)
  qed
  then show ?thesis
    using \<open>\<delta> > 0\<close> by blast
qed

lemma floor_step:
  assumes "0 \<le> t" "0 < h"
  shows "t - h \<le> real (nat \<lfloor>t / h\<rfloor>) * h" "real (nat \<lfloor>t / h\<rfloor>) * h \<le> t"
proof -
  have "0 \<le> t / h" using assms by simp
  then have eq: "real (nat \<lfloor>t / h\<rfloor>) = real_of_int \<lfloor>t / h\<rfloor>"
    by simp
  have "t / h < real_of_int \<lfloor>t / h\<rfloor> + 1" by simp
  then have "t < (real_of_int \<lfloor>t / h\<rfloor> + 1) * h"
    using \<open>0 < h\<close> by (simp only: pos_divide_less_eq)
  then show "t - h \<le> real (nat \<lfloor>t / h\<rfloor>) * h"
    by (simp add: eq algebra_simps)
  have "real_of_int \<lfloor>t / h\<rfloor> \<le> t / h" by simp
  then show "real (nat \<lfloor>t / h\<rfloor>) * h \<le> t"
    using \<open>0 < h\<close> by (simp only: eq pos_le_divide_eq)
qed

text \<open>Telescoping over \<open>\<lfloor>t / h\<rfloor>\<close> steps of size \<open>h\<close>.\<close>

lemma telescope_bound:
  fixes M E :: "real \<Rightarrow> 'a::real_normed_algebra_1"
  assumes M0: "M 0 = 1" and E0: "E 0 = 1"
    and Madd: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
    and Eadd: "\<And>s u. E (s + u) = E s * E u"
    and "0 \<le> t"
    and C: "\<And>s. s \<in> {0..t} \<Longrightarrow> norm (M s) \<le> C"
    and D: "\<And>s. s \<in> {0..t} \<Longrightarrow> norm (E s) \<le> D"
    and "0 < h"
  shows "norm (M (real (nat \<lfloor>t / h\<rfloor>) * h) * E (real (nat \<lfloor>t / h\<rfloor>) * h) - 1)
    \<le> t * C * D * norm ((1 / h) *\<^sub>R (M h * E h - 1))"
proof -
  define K where "K = nat \<lfloor>t / h\<rfloor>"
  define F where "F = (\<lambda>j::nat. M (real j * h) * E (real j * h))"
  have C0: "0 \<le> C" using C[of 0] \<open>0 \<le> t\<close> by (auto intro: order_trans[OF norm_ge_zero])
  have D0: "0 \<le> D" using D[of 0] \<open>0 \<le> t\<close> by (auto intro: order_trans[OF norm_ge_zero])
  have Kh: "real K * h \<le> t"
    unfolding K_def using floor_step[OF \<open>0 \<le> t\<close> \<open>0 < h\<close>] by simp
  have step: "F (Suc j) - F j = M (real j * h) * (M h * E h - 1) * E (real j * h)" for j
  proof -
    have "0 \<le> real j * h" using \<open>0 < h\<close> by simp
    then have a: "M (real (Suc j) * h) = M (real j * h) * M h"
      using Madd[of "real j * h" h] \<open>0 < h\<close> by (simp add: algebra_simps)
    have b: "E (real (Suc j) * h) = E h * E (real j * h)"
      using Eadd[of h "real j * h"] by (simp add: algebra_simps)
    show ?thesis
      unfolding F_def a b by (simp add: algebra_simps)
  qed
  have "F K - 1 = F K - F 0"
    by (simp add: F_def M0 E0)
  also have "\<dots> = (\<Sum>j<K. F (Suc j) - F j)"
    by (rule sum_lessThan_telescope[symmetric])
  also have "\<dots> = (\<Sum>j<K. M (real j * h) * (M h * E h - 1) * E (real j * h))"
    by (simp add: step)
  finally have tel: "F K - 1 = (\<Sum>j<K. M (real j * h) * (M h * E h - 1) * E (real j * h))" .
  have summand: "norm (M (real j * h) * (M h * E h - 1) * E (real j * h))
      \<le> C * norm (M h * E h - 1) * D" if "j \<in> {..<K}" for j
  proof -
    have jK: "real j * h \<le> real K * h"
      using that \<open>0 < h\<close> by (intro mult_right_mono) simp_all
    have js: "real j * h \<in> {0..t}"
      using order_trans[OF jK Kh] \<open>0 < h\<close> by simp
    have "norm (M (real j * h) * (M h * E h - 1) * E (real j * h))
        \<le> norm (M (real j * h)) * norm (M h * E h - 1) * norm (E (real j * h))"
      by (rule order_trans[OF norm_mult_ineq mult_right_mono[OF norm_mult_ineq norm_ge_zero]])
    also have "\<dots> \<le> C * norm (M h * E h - 1) * D"
      using C[OF js] D[OF js] C0
      by (intro mult_mono mult_right_mono) simp_all
    finally show ?thesis .
  qed
  have "norm (F K - 1) \<le> (\<Sum>j<K. C * norm (M h * E h - 1) * D)"
    unfolding tel by (rule order_trans[OF norm_sum sum_mono]) (rule summand)
  also have "\<dots> = real K * h * (C * D * norm ((1 / h) *\<^sub>R (M h * E h - 1)))"
    using \<open>0 < h\<close> by (simp add: abs_of_pos)
  also have "\<dots> \<le> t * (C * D * norm ((1 / h) *\<^sub>R (M h * E h - 1)))"
    using Kh C0 D0 by (intro mult_right_mono) simp_all
  finally show ?thesis
    by (simp add: F_def K_def mult.assoc)
qed

section \<open>Nonstandard analysis: standard parts of finite vectors\<close>

text \<open>
  The library provides standard parts of finite hyperreals. In a Heine--Borel space, every
  finite vector also has a standard part: the ultrafilter image of its representing sequence
  clusters at some point of a closed ball, and an ultrafilter that clusters at a point
  converges to it.
\<close>

lemma HFinite_approx_star_of:
  fixes x :: "'a::{real_normed_vector, heine_borel} star"
  assumes "x \<in> HFinite"
  shows "\<exists>a. x \<approx> star_of a"
proof -
  obtain X where x: "x = star_n X" by (cases x)
  then obtain u where u: "eventually (\<lambda>n. norm (X n) < u) \<U>"
    using assms HFinite_FreeUltrafilterNat_iff by blast
  define F where "F = filtermap X \<U>"
  have "F \<noteq> bot"
    by (simp add: F_def filtermap_bot_iff FreeUltrafilterNat.proper)
  moreover have "eventually (\<lambda>y. y \<in> cball 0 u) F"
    unfolding F_def eventually_filtermap by (rule eventually_mono[OF u]) simp
  ultimately obtain a where "inf (nhds a) F \<noteq> bot"
    using compact_filter[THEN iffD1, OF compact_cball[of 0 u]] by blast
  have lim: "eventually (\<lambda>n. X n \<in> S) \<U>" if "open S" "a \<in> S" for S
  proof (rule ccontr)
    assume "\<not> eventually (\<lambda>n. X n \<in> S) \<U>"
    then have "eventually (\<lambda>n. X n \<notin> S) \<U>"
      by (simp add: FreeUltrafilterNat.eventually_not_iff)
    then have "eventually (\<lambda>y. y \<notin> S) F"
      by (simp add: F_def eventually_filtermap)
    moreover have "eventually (\<lambda>y. y \<in> S) (nhds a)"
      using that by (rule eventually_nhds_in_open)
    ultimately have "eventually (\<lambda>y. False) (inf (nhds a) F)"
      unfolding eventually_inf by blast
    then show False
      using \<open>inf (nhds a) F \<noteq> bot\<close> by (simp add: eventually_False)
  qed
  have "x \<approx> star_of a"
    unfolding x star_of_def approx_FreeUltrafilterNat_iff
  proof (intro allI impI)
    fix r :: real
    assume "0 < r"
    then have "eventually (\<lambda>n. X n \<in> ball a r) \<U>"
      by (intro lim) simp_all
    then show "eventually (\<lambda>n. norm (X n - a) < r) \<U>"
      by (rule eventually_mono) (simp add: dist_norm norm_minus_commute)
  qed
  then show ?thesis ..
qed

section \<open>Euler's step\<close>

text \<open>
  If \<open>\<eta>\<close> is a positive infinitesimal and \<open>(M \<eta> - 1) / \<eta>\<close> is
  infinitely close to \<open>A\<close>, then \<open>M t = exp (t A)\<close>.
\<close>

lemma euler_step:
  fixes M :: "real \<Rightarrow> 'a::{real_normed_algebra_1, banach}" and A :: 'a
  assumes cont: "continuous_on {0..} M" and M0: "M 0 = 1"
    and add: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
    and eps: "\<eta> \<in> Infinitesimal" "0 < \<eta>"
    and gen: "( *f* (\<lambda>h. (1 / h) *\<^sub>R (M h - 1))) \<eta> \<approx> star_of A"
    and "0 \<le> t"
  shows "M t = exp (t *\<^sub>R A)"
proof (cases "t = 0")
  case True
  then show ?thesis using M0 by simp
next
  case False
  with \<open>0 \<le> t\<close> have "0 < t" by simp
  define E :: "real \<Rightarrow> 'a" where "E = (\<lambda>s. exp (s *\<^sub>R - A))"
  have E0: "E 0 = 1" by (simp add: E_def)
  have Eadd: "E (s + u) = E s * E u" for s u
    unfolding E_def scaleR_add_left by (rule exp_add_commuting) (simp add: algebra_simps)
  have Ederiv: "(E has_vector_derivative exp (s *\<^sub>R - A) * - A) (at s)" for s
    using exp_scaleR_has_vector_derivative_right[of "- A" s UNIV] by (simp add: E_def)
  have Econt: "isCont E s" for s
    using has_vector_derivative_continuous[OF Ederiv[of s]] .
  define F where "F = (\<lambda>s. M s * E s)"
  obtain C where C: "\<And>s. s \<in> {0..t} \<Longrightarrow> norm (M s) \<le> C"
  proof -
    have "bounded (M ` {0..t})"
      by (intro compact_imp_bounded compact_continuous_image continuous_on_subset[OF cont]) auto
    then obtain a where "\<forall>x \<in> M ` {0..t}. norm x \<le> a"
      unfolding bounded_iff ..
    then show ?thesis
      by (intro that[of a]) auto
  qed
  obtain D where D: "\<And>s. s \<in> {0..t} \<Longrightarrow> norm (E s) \<le> D"
  proof -
    have "bounded (E ` {0..t})"
      by (intro compact_imp_bounded compact_continuous_image)
        (auto intro: continuous_at_imp_continuous_on Econt)
    then obtain a where "\<forall>x \<in> E ` {0..t}. norm x \<le> a"
      unfolding bounded_iff ..
    then show ?thesis
      by (intro that[of a]) auto
  qed
  define Q where "Q = (\<lambda>h::real. (1 / h) *\<^sub>R (M h - 1))"
  define DE where "DE = (\<lambda>h::real. (1 / h) *\<^sub>R (E h - 1))"
  define G where "G = (\<lambda>h::real. (1 / h) *\<^sub>R (M h * E h - 1))"
  have G_split: "G = (\<lambda>h. Q h * E h + DE h)"
    by (simp add: fun_eq_iff G_def Q_def DE_def algebra_simps)

  txt \<open>At infinitesimal scale, \<open>(exp (- \<eta> A) - 1) / \<eta> \<approx> - A\<close>.\<close>
  define r where "r = (\<lambda>h::real. norm (E (0 + h) - E 0 - h *\<^sub>R - A) / norm h)"
  have "(E has_derivative (\<lambda>h. h *\<^sub>R - A)) (at 0)"
    using Ederiv[of 0] by (simp add: has_vector_derivative_def)
  then have "r \<midarrow>0\<rightarrow> 0"
    unfolding r_def by (simp add: has_derivative_at)
  then have r_ns: "r \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S 0"
    by (rule LIM_NSLIM)
  have DE_r: "\<forall>h. h \<noteq> 0 \<longrightarrow> norm (DE h - - A) = r h"
  proof (intro allI impI)
    fix h :: real
    assume "h \<noteq> 0"
    then have "DE h - - A = (1 / h) *\<^sub>R (E (0 + h) - E 0 - h *\<^sub>R - A)"
      by (simp add: DE_def E0 algebra_simps)
    then show "norm (DE h - - A) = r h"
      by (simp add: r_def divide_inverse mult.commute)
  qed
  have "\<forall>h. h \<noteq> 0 \<longrightarrow> hnorm (( *f* DE) h - star_of (- A)) = ( *f* r) h"
    using DE_r by transfer
  moreover have "\<eta> \<noteq> star_of 0" "\<eta> \<approx> star_of 0"
    using eps by (simp_all add: mem_infmal_iff)
  ultimately have "hnorm (( *f* DE) \<eta> - star_of (- A)) \<approx> 0"
    using r_ns unfolding NSLIM_def by auto
  then have DE_lim: "( *f* DE) \<eta> \<approx> star_of (- A)"
    by (simp add: approx_def mem_infmal_iff[symmetric] Infinitesimal_hnorm_iff)

  txt \<open>One step changes \<open>M s * E s\<close> by \<open>\<eta>\<close> times an infinitesimal.\<close>
  have E_eps: "( *f* E) \<eta> \<approx> star_of 1"
    using isCont_isNSCont[OF Econt[of 0]] \<open>\<eta> \<approx> star_of 0\<close> E0
    unfolding isNSCont_def by auto
  have "( *f* G) \<eta> = ( *f* Q) \<eta> * ( *f* E) \<eta> + ( *f* DE) \<eta>"
    by (simp add: G_split)
  moreover have "( *f* Q) \<eta> * ( *f* E) \<eta> + ( *f* DE) \<eta> \<approx> star_of A * star_of 1 + star_of (- A)"
    using gen E_eps DE_lim unfolding Q_def by (intro approx_add approx_mult_star_of)
  ultimately have G_inf: "( *f* G) \<eta> \<in> Infinitesimal"
    by (simp add: mem_infmal_iff)

  txt \<open>Over \<open>\<lfloor>t / \<eta>\<rfloor>\<close> steps the changes add up to an infinitesimal.\<close>
  define K where "K = (\<lambda>h::real. real (nat \<lfloor>t / h\<rfloor>) * h)"
  have "\<forall>h. 0 < h \<longrightarrow> norm (F (K h) - 1) \<le> t * C * D * norm (G h)"
    using telescope_bound[of M E, OF M0 E0 add Eadd \<open>0 \<le> t\<close> C D] by (simp add: F_def K_def G_def)
  then have "\<forall>h. 0 < h \<longrightarrow>
      hnorm (( *f* (\<lambda>h. F (K h) - 1)) h) \<le> star_of (t * C * D) * hnorm (( *f* G) h)"
    by transfer
  then have FK_le: "hnorm (( *f* (\<lambda>h. F (K h) - 1)) \<eta>) \<le> star_of (t * C * D) * hnorm (( *f* G) \<eta>)"
    using eps by blast
  have "star_of (t * C * D) * hnorm (( *f* G) \<eta>) \<in> Infinitesimal"
    using G_inf by (intro Infinitesimal_star_of_mult2) (simp add: Infinitesimal_hnorm_iff)
  then have "hnorm (( *f* (\<lambda>h. F (K h) - 1)) \<eta>) \<in> Infinitesimal"
    using Infinitesimal_interval2[OF _ Infinitesimal_zero _ FK_le] by simp
  then have FK: "( *f* (\<lambda>h. F (K h) - 1)) \<eta> \<approx> 0"
    by (simp add: Infinitesimal_hnorm_iff mem_infmal_iff[symmetric])

  txt \<open>\<open>\<lfloor>t / \<eta>\<rfloor> \<eta> \<approx> t\<close>, and \<open>M s * E s\<close> is continuous at \<open>t\<close>.\<close>
  have "\<forall>h. 0 < h \<longrightarrow> star_of t - h \<le> ( *f* K) h \<and> ( *f* K) h \<le> star_of t"
    by transfer (auto simp only: K_def intro: floor_step[OF \<open>0 \<le> t\<close>])
  then have K1: "star_of t - \<eta> \<le> ( *f* K) \<eta>" and K2: "( *f* K) \<eta> \<le> star_of t"
    using eps by blast+
  have "star_of t - ( *f* K) \<eta> \<in> Infinitesimal"
    by (rule Infinitesimal_interval2[of \<eta> 0]) (use eps K1 K2 in \<open>simp_all add: algebra_simps\<close>)
  then have "star_of t \<approx> ( *f* K) \<eta>"
    by (simp add: approx_def)
  then have K_approx: "( *f* K) \<eta> \<approx> star_of t"
    by (rule approx_sym)
  have "isCont M t"
    using continuous_on_interior[OF cont] \<open>0 < t\<close> by simp
  then have "isCont F t"
    unfolding F_def using Econt by simp
  then have "( *f* F) (( *f* K) \<eta>) \<approx> star_of (F t)"
    using K_approx unfolding isNSCont_isCont_iff[symmetric] isNSCont_def by blast
  moreover have "\<forall>h. ( *f* F) (( *f* K) h) = ( *f* (\<lambda>h. F (K h) - 1)) h + 1"
    by transfer simp
  then have "( *f* F) (( *f* K) \<eta>) = ( *f* (\<lambda>h. F (K h) - 1)) \<eta> + 1" ..
  moreover have "( *f* (\<lambda>h. F (K h) - 1)) \<eta> + 1 \<approx> 0 + 1"
    using FK by (rule approx_add) simp
  ultimately have "star_of (F t) \<approx> star_of 1"
    by (metis approx_sym approx_trans add_0 star_of_one)
  then have F1: "M t * exp (t *\<^sub>R - A) = 1"
    by (simp only: star_of_approx_iff) (simp add: F_def E_def)
  have "exp (t *\<^sub>R - A) * exp (t *\<^sub>R A) = 1"
    using exp_add_commuting[of "- (t *\<^sub>R A)" "t *\<^sub>R A"] by simp
  then have "M t = M t * exp (t *\<^sub>R - A) * exp (t *\<^sub>R A)"
    by (simp add: mult.assoc)
  then show ?thesis
    unfolding F1 by simp
qed

section \<open>The semigroup theorem\<close>

theorem semigroup_eq_exp:
  fixes M :: "real \<Rightarrow> 'a::{real_normed_algebra_1, banach, heine_borel}"
  assumes cont: "continuous_on {0..} M" and M0: "M 0 = 1"
    and add: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
  shows "\<exists>A. \<forall>t\<ge>0. M t = exp (t *\<^sub>R A)"
proof -
  have "continuous (at 0 within {0..}) M"
    using cont by (simp add: continuous_on_eq_continuous_within)
  then obtain \<delta> C where "\<delta> > 0" and bound:
    "\<And>n. norm ((1 / (\<delta> / real (Suc n))) *\<^sub>R (M (\<delta> / real (Suc n)) - 1)) \<le> C"
    using exists_bounded_quotients[of M, OF _ M0 add] by blast
  define Q where "Q = (\<lambda>h::real. (1 / h) *\<^sub>R (M h - 1))"
  define e where "e = (\<lambda>n. \<delta> / real (Suc n))"

  txt \<open>The infinitesimal step \<open>\<eta> = \<delta> / \<omega>\<close>.\<close>
  define \<eta> where "\<eta> = ( *f* e) whn"
  have "e \<longlonglongrightarrow> 0"
    using tendsto_mult_left_zero[OF LIMSEQ_inverse_real_of_nat, of \<delta>]
    by (simp add: e_def divide_inverse mult.commute)
  then have "\<eta> \<approx> star_of 0"
    unfolding \<eta>_def using LIMSEQ_NSLIMSEQ NSLIMSEQ_def HNatInfinite_whn by blast
  then have eps_inf: "\<eta> \<in> Infinitesimal"
    by (simp add: mem_infmal_iff)
  have "\<forall>N. 0 < ( *f* e) N"
    by transfer (simp add: e_def \<open>\<delta> > 0\<close>)
  then have eps_pos: "0 < \<eta>"
    by (simp add: \<eta>_def)

  txt \<open>By transfer, \<open>(M \<eta> - 1) / \<eta>\<close> is finite, so it has a standard part.\<close>
  have "\<forall>N. hnorm (( *f* Q) (( *f* e) N)) \<le> star_of C"
    by transfer (unfold Q_def e_def, intro allI bound)
  then have "hnorm (( *f* Q) \<eta>) < star_of (C + 1)"
    unfolding \<eta>_def by (meson le_less_trans less_add_one star_of_less)
  then have "( *f* Q) \<eta> \<in> HFinite"
    unfolding HFinite_def mem_Collect_eq by (rule bexI[OF _ SReal_hypreal_of_real])
  then obtain A where "( *f* Q) \<eta> \<approx> star_of A"
    using HFinite_approx_star_of by blast
  then have "\<forall>t\<ge>0. M t = exp (t *\<^sub>R A)"
    using euler_step[of M, OF cont M0 add eps_inf eps_pos] unfolding Q_def by blast
  then show ?thesis ..
qed

end
