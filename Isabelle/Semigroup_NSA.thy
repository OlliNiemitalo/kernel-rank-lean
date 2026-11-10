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

  Fix a positive infinitesimal \<open>\<epsilon>\<close>. In the time \<open>\<epsilon>\<close> the semigroup changes by
  \<open>x = M \<epsilon> - 1\<close>, which is infinitesimal too. The generator should be the standard part of
  \<open>x / \<epsilon>\<close>, but that quotient might be infinite. So measure the time and the change on the
  common scale \<open>\<eta> = \<epsilon> + \<parallel>x\<parallel>\<close> instead. As \<open>\<epsilon> / \<eta> + \<parallel>x / \<eta>\<parallel> = 1\<close>, both are finite:
  \<open>x / \<eta>\<close> has a standard part \<open>B\<close>, and \<open>\<epsilon> / \<eta> \<approx> a = 1 - \<parallel>B\<parallel>\<close>. The pair \<open>(a, B)\<close> is the
  generator in homogeneous coordinates.

  \<^enum> Euler's step. The elements \<open>u = M \<epsilon>\<close> and \<open>v = exp (\<eta> B)\<close> differ by \<open>\<eta>\<close> times an
    infinitesimal. Both have norm at most \<open>exp \<eta>\<close>. A noncommutative power estimate gives
    \<open>\<parallel>u^N - v^N\<parallel> \<le> N \<eta> exp (N \<eta>) \<parallel>(u - v) / \<eta>\<parallel>\<close>. Choose a hypernatural \<open>N\<close> with
    \<open>s - \<eta> \<le> N \<eta> \<le> s\<close> for standard \<open>s \<ge> 0\<close>. The bound is infinitesimal, and continuity at
    \<open>N \<epsilon> \<approx> s a\<close> and \<open>N \<eta> \<approx> s\<close> gives \<open>M (s a) = exp (s B)\<close>.
  \<^enum> The semigroup is not infinitely fast: \<open>a = 0\<close> would give \<open>exp (s B) = M 0 = 1\<close> for all
    \<open>s \<ge> 0\<close>, so \<open>B = 0\<close> and \<open>a = 1\<close>. Hence \<open>M t = exp (t (B / a))\<close>.
\<close>

section \<open>Ordinary analysis: powers in a normed algebra\<close>

text \<open>
  The recurrence \<open>x^(n+1) - y^(n+1) = x (x^n - y^n) + (x - y) y^n\<close> compares powers without
  requiring \<open>x\<close> and \<open>y\<close> to commute. The slightly loose factor \<open>exp (n h)\<close> also covers \<open>n = 0\<close>.
\<close>

lemma power_difference_bound:
  fixes x y :: "'a::real_normed_algebra_1"
  assumes hx: "norm x \<le> exp h" and hy: "norm y \<le> exp h" and h: "0 \<le> h"
  shows "norm (x ^ n - y ^ n) \<le> real n * exp (real n * h) * norm (x - y)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "norm (y ^ n) \<le> exp (real n * h)"
    using norm_power_ineq[of y n] power_mono[OF hy norm_ge_zero, of n]
    by (simp add: exp_of_nat_mult)
  also have "\<dots> \<le> exp (real (Suc n) * h)"
    using h by (simp add: algebra_simps)
  finally have yp: "norm (y ^ n) \<le> exp (real (Suc n) * h)" .
  have eq: "x ^ Suc n - y ^ Suc n = x * (x ^ n - y ^ n) + (x - y) * y ^ n"
    by (simp add: algebra_simps)
  have "norm (x ^ Suc n - y ^ Suc n)
      \<le> norm x * norm (x ^ n - y ^ n) + norm (x - y) * norm (y ^ n)"
    unfolding eq by (intro order_trans[OF norm_triangle_ineq add_mono] norm_mult_ineq)
  also have "\<dots> \<le> exp h * (real n * exp (real n * h) * norm (x - y))
      + norm (x - y) * exp (real (Suc n) * h)"
    by (intro add_mono mult_mono hx Suc.IH yp order_refl norm_ge_zero) simp_all
  also have "\<dots> = real (Suc n) * exp (real (Suc n) * h) * norm (x - y)"
    by (simp add: exp_add algebra_simps)
  finally show ?case .
qed

lemma semigroup_power:
  fixes M :: "real \<Rightarrow> 'a::monoid_mult"
  assumes M0: "M 0 = 1"
    and add: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
    and h: "0 \<le> h"
  shows "M (real n * h) = M h ^ n"
  by (induction n) (simp_all add: M0 add h algebra_simps power_Suc2)

section \<open>Nonstandard analysis: standard parts and continuity\<close>

text \<open>
  The library provides standard parts of finite hyperreals. In a Heine--Borel space, a vector
  \<open>x\<close> with \<open>\<parallel>x\<parallel> \<le> r\<close> also has a standard part, in the closed ball of radius \<open>r\<close>: the
  ultrafilter image of its representing sequence clusters at some point of that ball, and an
  ultrafilter that clusters at a point converges to it.
\<close>

lemma standard_part:
  fixes x :: "'a::{real_normed_vector, heine_borel} star"
  assumes "hnorm x \<le> star_of r"
  obtains a where "x \<approx> star_of a" "norm a \<le> r"
proof -
  obtain X where x: "x = star_n X" by (cases x)
  then have "eventually (\<lambda>n. norm (X n) \<le> r) \<U>"
    using assms by (simp add: hnorm_def starfun_star_n star_of_def star_n_le)
  then have "eventually (\<lambda>y. y \<in> cball 0 r) (filtermap X \<U>)"
    by (simp add: eventually_filtermap)
  moreover have "filtermap X \<U> \<noteq> bot"
    by (simp add: filtermap_bot_iff FreeUltrafilterNat.proper)
  ultimately obtain a where a: "a \<in> cball 0 r" "inf (nhds a) (filtermap X \<U>) \<noteq> bot"
    using compact_filter[THEN iffD1, OF compact_cball[of 0 r]] by blast
  have lim: "eventually (\<lambda>n. X n \<in> S) \<U>" if "open S" "a \<in> S" for S
  proof (rule ccontr)
    assume "\<not> eventually (\<lambda>n. X n \<in> S) \<U>"
    then have "eventually (\<lambda>y. y \<notin> S) (filtermap X \<U>)"
      by (simp add: FreeUltrafilterNat.eventually_not_iff eventually_filtermap)
    then have "eventually (\<lambda>y. False) (inf (nhds a) (filtermap X \<U>))"
      using eventually_nhds_in_open[OF that] unfolding eventually_inf by blast
    then show False
      using a(2) by (simp add: eventually_False)
  qed
  have "x \<approx> star_of a"
    unfolding x star_of_def approx_FreeUltrafilterNat_iff
    using lim[OF open_ball, of a] by (simp add: dist_norm norm_minus_commute)
  then show ?thesis
    using a(1) by (intro that) simp_all
qed

text \<open>
  Extend \<open>f\<close> by \<open>f (max t 0)\<close> to use the library's nonstandard continuity on the whole line.
  At nonnegative standard and nonstandard arguments, the extension agrees with \<open>f\<close>.
\<close>

lemma approx_continuous_halfline:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes cont: "continuous_on {0..} f"
    and a: "0 \<le> a" and x: "0 \<le> x" "x \<approx> star_of a"
  shows "( *f* f) x \<approx> star_of (f a)"
proof -
  have "continuous_on UNIV (f \<circ> (\<lambda>t. max t 0))"
    by (intro continuous_on_compose continuous_intros continuous_on_subset[OF cont]) auto
  then have cont': "isCont (f \<circ> (\<lambda>t. max t 0)) a"
    by (simp add: continuous_on_eq_continuous_at o_def)
  have "( *f* (f \<circ> (\<lambda>t. max t 0))) x \<approx> star_of (f (max a 0))"
    using isNSContD[OF isCont_isNSCont[OF cont'] x(2)] by simp
  moreover have "\<And>y. 0 \<le> y \<Longrightarrow> ( *f* (f \<circ> (\<lambda>t. max t 0))) y = ( *f* f) y"
    by transfer simp
  ultimately show ?thesis
    using a x(1) by simp
qed

section \<open>The semigroup theorem\<close>

theorem semigroup_eq_exp:
  fixes M :: "real \<Rightarrow> 'a::{real_normed_algebra_1, banach, heine_borel}"
  assumes cont: "continuous_on {0..} M" and M0: "M 0 = 1"
    and add: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
  shows "\<exists>A. \<forall>t\<ge>0. M t = exp (t *\<^sub>R A)"
proof -
  define \<eta> where "\<eta> = (\<lambda>h. h + norm (M h - 1))"
  define Q where "Q = (\<lambda>h. (M h - 1) /\<^sub>R \<eta> h)"
  let ?\<eta> = "( *f* \<eta>) \<epsilon>" and ?Q = "( *f* Q) \<epsilon>"

  txt \<open>The scale \<open>\<eta>\<close> is a positive infinitesimal, because \<open>M \<epsilon> \<approx> M 0\<close>.\<close>
  have "( *f* M) \<epsilon> \<approx> star_of (M 0)"
    by (intro approx_continuous_halfline[OF cont]) (simp_all add: epsilon_gt_zero less_imp_le)
  moreover have "\<And>h. ( *f* \<eta>) h = h + hnorm (( *f* M) h - 1)"
    unfolding \<eta>_def by transfer (rule refl)
  ultimately have \<eta>0: "?\<eta> \<in> Infinitesimal"
    by (simp add: M0 approx_def Infinitesimal_add Infinitesimal_hnorm_iff)

  txt \<open>On that scale, the change has a standard part \<open>B\<close>, and the time is close to \<open>a\<close>.\<close>
  have scale: "\<forall>h>0. 0 < \<eta> h \<and> h / \<eta> h + norm (Q h) = 1"
    by (auto simp: \<eta>_def Q_def divide_simps add_pos_nonneg add_nonneg_eq_0_iff)
  then have "\<forall>h>0. 0 < ( *f* \<eta>) h \<and> h / ( *f* \<eta>) h + hnorm (( *f* Q) h) = 1"
    by transfer
  then have \<eta>pos: "0 < ?\<eta>" and sum: "\<epsilon> / ?\<eta> = 1 - hnorm ?Q"
    using epsilon_gt_zero by (simp_all add: eq_diff_eq)
  then have "hnorm ?Q \<le> star_of 1"
    using epsilon_gt_zero divide_nonneg_pos[of \<epsilon> ?\<eta>] by simp
  then obtain B where B: "?Q \<approx> star_of B" "norm B \<le> 1"
    by (rule standard_part)
  define a where "a = 1 - norm B"
  have a: "0 \<le> a" "\<epsilon> / ?\<eta> \<approx> star_of a"
    using approx_diff[OF approx_refl approx_hnorm[OF B(1)], of 1] B(2)
    by (simp_all add: a_def sum)

  txt \<open>The exponential \<open>E u = exp (u B)\<close> takes the same step on that scale, to first order.\<close>
  define E where "E = (\<lambda>u. exp (u *\<^sub>R B))"
  define DE where "DE = (\<lambda>u. (E u - 1) /\<^sub>R u)"
  have E0: "E 0 = 1"
    by (simp add: E_def)
  have Eadd: "E (u + v) = E u * E v" for u v
    unfolding E_def scaleR_add_left by (rule exp_add_commuting) (simp add: algebra_simps)
  have Ederiv: "(E has_vector_derivative E u * B) (at u)" for u
    using exp_scaleR_has_vector_derivative_right[of B u UNIV] by (simp add: E_def)
  have "(DE \<longlongrightarrow> B) (at 0)"
    using Ederiv[of 0] unfolding has_vector_derivative_within_1D by (simp add: DE_def E0)
  then have DE: "( *f* DE) ?\<eta> \<approx> star_of B"
    using \<eta>pos \<eta>0 by (auto dest!: LIM_NSLIM simp: NSLIM_def mem_infmal_iff)
  have error: "?Q - ( *f* DE) ?\<eta> \<in> Infinitesimal"
    using approx_diff[OF B(1) DE] by (simp add: mem_infmal_iff)

  txt \<open>The power estimate controls all step counts without compact-interval bounds.\<close>
  have "\<forall>n h. 0 < h \<longrightarrow>
      norm (M (real n * h) - E (real n * \<eta> h))
        \<le> real n * \<eta> h * exp (real n * \<eta> h) * norm (Q h - DE (\<eta> h))"
  proof (intro allI impI)
    fix n :: nat and h :: real
    assume h: "0 < h"
    have pos: "0 < \<eta> h"
      using scale h by simp
    have "norm (M h) \<le> 1 + norm (M h - 1)"
      using norm_triangle_ineq[of 1 "M h - 1"] by simp
    also have "\<dots> \<le> 1 + \<eta> h"
      using h by (simp add: \<eta>_def)
    also have "\<dots> \<le> exp (\<eta> h)"
      by simp
    finally have Mh: "norm (M h) \<le> exp (\<eta> h)" .
    have Eh: "norm (E (\<eta> h)) \<le> exp (\<eta> h)"
      using B(2) pos by (auto simp: E_def abs_of_pos intro!: order_trans[OF norm_exp])
    have eq: "M h - E (\<eta> h) = \<eta> h *\<^sub>R (Q h - DE (\<eta> h))"
      using pos by (simp add: Q_def DE_def algebra_simps)
    have "norm (M h ^ n - E (\<eta> h) ^ n)
        \<le> real n * exp (real n * \<eta> h) * norm (M h - E (\<eta> h))"
      by (rule power_difference_bound[OF Mh Eh less_imp_le[OF pos]])
    then show "norm (M (real n * h) - E (real n * \<eta> h))
        \<le> real n * \<eta> h * exp (real n * \<eta> h) * norm (Q h - DE (\<eta> h))"
      by (simp only: semigroup_power[of M, OF M0 add less_imp_le[OF h]]
        semigroup_power[of E, OF E0 Eadd less_imp_le[OF pos]] eq norm_scaleR abs_of_pos[OF pos])
        (simp add: mult_ac)
  qed
  then have bound: "\<forall>n h. 0 < h \<longrightarrow>
      hnorm (( *f* M) (of_hypnat n * h) - ( *f* E) (of_hypnat n * ( *f* \<eta>) h))
        \<le> of_hypnat n * ( *f* \<eta>) h * ( *f* exp) (of_hypnat n * ( *f* \<eta>) h)
          * hnorm (( *f* Q) h - ( *f* DE) (( *f* \<eta>) h))"
    by transfer

  txt \<open>Take a hypernatural number \<open>N\<close> of steps with \<open>s - \<eta> \<le> N \<eta> \<le> s\<close>.\<close>
  have main: "M (s * a) = E s" if s: "0 \<le> s" for s
  proof -
    have "\<exists>n. s - k \<le> real n * k \<and> real n * k \<le> s" if "0 < k" for k
      using floor_divide_lower[of k s] floor_divide_upper[of k s] s that
      by (intro exI[of _ "nat \<lfloor>s / k\<rfloor>"]) (simp add: algebra_simps)
    then have "\<forall>k>0. \<exists>n. star_of s - k \<le> of_hypnat n * k \<and> of_hypnat n * k \<le> star_of s"
      by transfer blast
    then obtain N where N: "star_of s - ?\<eta> \<le> of_hypnat N * ?\<eta>" "of_hypnat N * ?\<eta> \<le> star_of s"
      using \<eta>pos by blast
    let ?N = "of_hypnat N :: hypreal"
    have N\<eta>: "?N * ?\<eta> \<approx> star_of s"
      using N \<eta>0
      by (metis Infinitesimal_approx_minus add_diff_cancel_left' approx_le_bound approx_sym
        diff_diff_eq2)
    have "( *f* exp) (?N * ?\<eta>) \<approx> star_of (exp s)"
      by (intro isNSContD isCont_isNSCont N\<eta> continuous_intros)
    then have finite: "?N * ?\<eta> * ( *f* exp) (?N * ?\<eta>) \<in> HFinite"
      using N\<eta> by (meson HFinite_mult approx_star_of_HFinite)
    have close: "( *f* M) (?N * \<epsilon>) \<approx> ( *f* E) (?N * ?\<eta>)"
      using bound[rule_format, OF epsilon_gt_zero, of N] error finite
      by (meson Infinitesimal_HFinite_mult2 Infinitesimal_approx_minus Infinitesimal_hnorm_iff
        hnorm_le_Infinitesimal)
    have "?N * \<epsilon> = ?N * ?\<eta> * (\<epsilon> / ?\<eta>)"
      using \<eta>pos by simp
    then have "( *f* M) (?N * \<epsilon>) \<approx> star_of (M (s * a))"
      using approx_mult_star_of[OF N\<eta> a(2)] s a(1)
      by (intro approx_continuous_halfline[OF cont]) (simp_all add: epsilon_gt_zero less_imp_le)
    moreover have "( *f* E) (?N * ?\<eta>) \<approx> star_of (E s)"
      by (intro isNSContD isCont_isNSCont N\<eta> has_vector_derivative_continuous[OF Ederiv])
    ultimately show ?thesis
      using close by (metis approx_trans3 star_of_approx_iff)
  qed

  txt \<open>The semigroup is not infinitely fast.\<close>
  have "a \<noteq> 0"
  proof
    assume "a = 0"
    then have "\<forall>u>0. DE u = 0"
      using main M0 by (simp add: DE_def)
    then have "\<forall>u>0. ( *f* DE) u = 0"
      by transfer
    then show False
      using DE \<eta>pos \<open>a = 0\<close> by (simp add: a_def)
  qed
  then have "M t = exp (t *\<^sub>R (B /\<^sub>R a))" if "0 \<le> t" for t
    using main[of "t / a"] that a(1) by (simp add: E_def flip: divide_inverse)
  then show ?thesis
    by blast
qed

end
