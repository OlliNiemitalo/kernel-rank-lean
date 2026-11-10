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

  \<^enum> Euler's step. For \<open>E u = exp (u B)\<close>, the steps \<open>M \<epsilon>\<close> and \<open>E \<eta>\<close> differ by \<open>\<eta>\<close> times an
    infinitesimal, because \<open>(M \<epsilon> - 1) / \<eta> \<approx> B \<approx> (E \<eta> - 1) / \<eta>\<close>. Take \<open>N\<close> steps, with
    \<open>N \<eta> \<approx> s\<close> for a standard \<open>s \<ge> 0\<close>. Replacing the steps of \<open>M\<close> by those of \<open>E\<close>, one at
    a time, changes the result by \<open>N \<eta>\<close> times an infinitesimal. The semigroup \<open>M\<close> arrives
    at the time \<open>N \<epsilon> \<approx> s a\<close> and \<open>E\<close> at the time \<open>N \<eta> \<approx> s\<close>, so \<open>M (s a) = exp (s B)\<close>.
  \<^enum> The semigroup is not infinitely fast: \<open>a = 0\<close> would give \<open>exp (s B) = M 0 = 1\<close> for all
    \<open>s \<ge> 0\<close>, so \<open>B = 0\<close> and \<open>a = 1\<close>. Hence \<open>M t = exp (t (B / a))\<close>.
\<close>

section \<open>Ordinary analysis: replacing the steps of one semigroup by those of another\<close>

lemma floor_step:
  assumes "0 \<le> t" "0 < h"
  shows "\<exists>n. t - h \<le> real n * h \<and> real n * h \<le> t"
  using floor_divide_lower[of h t] floor_divide_upper[of h t] assms
  by (intro exI[of _ "nat \<lfloor>t / h\<rfloor>"]) (simp add: algebra_simps)

text \<open>
  Let \<open>M\<close> take \<open>n\<close> steps of size \<open>h\<close>, followed by \<open>E\<close> for a time \<open>r\<close>. Each step of \<open>M\<close>
  can be replaced by a step of size \<open>k\<close> of \<open>E\<close> at the cost of \<open>C D \<parallel>M h - E k\<parallel>\<close>, where \<open>C\<close>
  and \<open>D\<close> bound \<open>M\<close> and \<open>E\<close> on \<open>[0, t]\<close>.
\<close>

lemma replace_steps:
  fixes M E :: "real \<Rightarrow> 'a::real_normed_algebra_1"
  assumes M0: "M 0 = 1"
    and Madd: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
    and Eadd: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> E (s + t) = E s * E t"
    and C: "\<And>u. u \<in> {0..t} \<Longrightarrow> norm (M u) \<le> C"
    and D: "\<And>u. u \<in> {0..t} \<Longrightarrow> norm (E u) \<le> D"
    and hk: "0 \<le> h" "0 \<le> k"
  shows "0 \<le> r \<Longrightarrow> real n * h \<le> t \<Longrightarrow> real n * k + r \<le> t \<Longrightarrow>
    norm (M (real n * h) * E r - E (real n * k + r)) \<le> real n * (C * D * norm (M h - E k))"
proof (induction n arbitrary: r)
  case 0
  then show ?case
    by (simp add: M0)
next
  case (Suc n)
  define u where "u = real n * h"
  have nn: "0 \<le> u" "0 \<le> real n * k"
    using hk by (simp_all add: u_def)
  then have "u \<le> t" "r \<le> t" and rest: "real n * k + (k + r) \<le> t"
    using Suc.prems hk unfolding u_def of_nat_Suc distrib_right by linarith+
  then have t: "u \<in> {0..t}" "r \<in> {0..t}"
    using nn Suc.prems by simp_all
  have CD: "0 \<le> C" "0 \<le> D"
    using C[OF t(1)] D[OF t(2)] by (auto intro: order_trans[OF norm_ge_zero])
  have eq: "M (real (Suc n) * h) * E r - E (real (Suc n) * k + r)
      = M u * (M h - E k) * E r + (M u * E (k + r) - E (real n * k + (k + r)))"
    using Madd[OF nn(1) hk(1)] Eadd[OF hk(2) Suc.prems(1)] by (simp add: u_def algebra_simps)
  have "norm (M u * (M h - E k) * E r) \<le> norm (M u) * norm (M h - E k) * norm (E r)"
    by (rule order_trans[OF norm_mult_ineq mult_right_mono[OF norm_mult_ineq norm_ge_zero]])
  also have "\<dots> \<le> C * norm (M h - E k) * D"
    using C[OF t(1)] D[OF t(2)] CD by (intro mult_mono mult_right_mono) simp_all
  finally have "norm (M u * (M h - E k) * E r + (M u * E (k + r) - E (real n * k + (k + r))))
      \<le> C * norm (M h - E k) * D + real n * (C * D * norm (M h - E k))"
    using Suc.IH[of "k + r"] Suc.prems(1) hk t rest unfolding u_def
    by (intro order_trans[OF norm_triangle_ineq add_mono]) simp_all
  then show ?case
    unfolding eq by (simp add: algebra_simps)
qed

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
  A function that is continuous on a set \<open>S\<close> maps points of \<open>*S\<close> that are infinitely close to
  \<open>a \<in> S\<close> to points infinitely close to \<open>f a\<close>. The library has this for \<open>S = UNIV\<close>.
\<close>

lemma approx_continuous_on:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous_on S f" "a \<in> S" "x \<in> *s* S" "x \<approx> star_of a"
  shows "( *f* f) x \<approx> star_of (f a)"
proof -
  have "hnorm (( *f* f) x - star_of (f a)) < star_of r" if "0 < r" for r
  proof -
    obtain d where "0 < d" and "\<forall>y\<in>S. norm (y - a) < d \<longrightarrow> norm (f y - f a) < r"
      using assms(1,2) \<open>0 < r\<close> unfolding continuous_on_iff dist_norm by blast
    then have "\<forall>y\<in>*s* S. hnorm (y - star_of a) < star_of d
        \<longrightarrow> hnorm (( *f* f) y - star_of (f a)) < star_of r"
      by transfer
    then show ?thesis
      using assms(3,4) \<open>0 < d\<close> by (simp add: approx_def InfinitesimalD2)
  qed
  then show ?thesis
    by (simp add: approx_def InfinitesimalI2)
qed

lemma starset_atLeast: "\<And>x. x \<in> *s* {a..} \<longleftrightarrow> star_of a \<le> x"
  by transfer simp

section \<open>Euler's step\<close>

text \<open>
  Two continuous semigroups whose infinitesimal steps agree to first order are equal, up to a
  change of speed. Let \<open>M\<close> take the step \<open>\<delta>\<close> while \<open>E\<close> takes the step \<open>\<eta>\<close>, with
  \<open>\<delta> / \<eta> \<approx> a\<close>. If \<open>M \<delta>\<close> and \<open>E \<eta>\<close> differ by \<open>\<eta>\<close> times an infinitesimal, then
  \<open>M (s a) = E s\<close>.
\<close>

lemma euler_step:
  fixes M E :: "real \<Rightarrow> 'a::real_normed_algebra_1"
  assumes M: "continuous_on {0..} M" "M 0 = 1"
      "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
    and E: "continuous_on {0..} E" "E 0 = 1"
      "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> E (s + t) = E s * E t"
    and \<delta>: "0 \<le> \<delta>" "\<delta> \<le> \<eta>" and \<eta>: "0 < \<eta>" "\<eta> \<in> Infinitesimal"
    and a: "0 \<le> a" "\<delta> / \<eta> \<approx> star_of a"
    and step: "hnorm (( *f* M) \<delta> - ( *f* E) \<eta>) / \<eta> \<in> Infinitesimal"
    and s: "0 \<le> s"
  shows "M (s * a) = E s"
proof -
  have bounded: "\<exists>C. \<forall>u\<in>{0..s}. norm (f u) \<le> C" if "continuous_on {0..} f" for f :: "real \<Rightarrow> 'a"
  proof -
    have "bounded (f ` {0..s})"
      by (intro compact_imp_bounded compact_continuous_image continuous_on_subset[OF that]) auto
    then show ?thesis
      by (auto simp: bounded_iff)
  qed
  obtain C D where C: "\<And>u. u \<in> {0..s} \<Longrightarrow> norm (M u) \<le> C"
      and D: "\<And>u. u \<in> {0..s} \<Longrightarrow> norm (E u) \<le> D"
    using bounded[OF M(1)] bounded[OF E(1)] by blast

  txt \<open>Take \<open>N\<close> steps, where \<open>N \<eta> \<le> s < (N + 1) \<eta>\<close>.\<close>
  have "\<forall>k>0. \<exists>n. s - k \<le> real n * k \<and> real n * k \<le> s"
    using floor_step[OF s] by blast
  then have "\<forall>k>0. \<exists>n. star_of s - k \<le> of_hypnat n * k \<and> of_hypnat n * k \<le> star_of s"
    by transfer
  then obtain N where N: "star_of s - \<eta> \<le> of_hypnat N * \<eta>" "of_hypnat N * \<eta> \<le> star_of s"
    using \<eta>(1) by blast
  let ?N = "of_hypnat N :: hypreal"
  have N\<eta>: "?N * \<eta> \<approx> star_of s"
    using N \<eta>(2)
    by (metis Infinitesimal_approx_minus add_diff_cancel_left' approx_le_bound approx_sym
      diff_diff_eq2)

  txt \<open>Replacing the steps of \<open>M\<close> by those of \<open>E\<close> changes the result by \<open>N \<eta>\<close> times an
    infinitesimal.\<close>
  have "\<forall>n h k. 0 \<le> h \<and> 0 \<le> k \<and> real n * h \<le> s \<and> real n * k \<le> s \<longrightarrow>
      norm (M (real n * h) - E (real n * k)) \<le> real n * (C * D * norm (M h - E k))"
    using replace_steps[of M E s C D _ _ 0, OF M(2,3) E(3) C D] by (simp add: E(2))
  then have "\<forall>n h k. 0 \<le> h \<and> 0 \<le> k \<and> of_hypnat n * h \<le> star_of s \<and> of_hypnat n * k \<le> star_of s \<longrightarrow>
      hnorm (( *f* M) (of_hypnat n * h) - ( *f* E) (of_hypnat n * k))
        \<le> of_hypnat n * (star_of (C * D) * hnorm (( *f* M) h - ( *f* E) k))"
    by transfer
  moreover have "?N * \<delta> \<le> ?N * \<eta>"
    using \<delta>(2) by (intro mult_left_mono) simp_all
  ultimately have "hnorm (( *f* M) (?N * \<delta>) - ( *f* E) (?N * \<eta>))
      \<le> ?N * (star_of (C * D) * hnorm (( *f* M) \<delta> - ( *f* E) \<eta>))"
    using N(2) \<delta>(1) \<eta>(1) by (simp add: less_imp_le)
  also have "\<dots> = ?N * \<eta> * (star_of (C * D) * (hnorm (( *f* M) \<delta> - ( *f* E) \<eta>) / \<eta>))"
    using \<eta>(1) by simp
  finally have close: "( *f* M) (?N * \<delta>) \<approx> ( *f* E) (?N * \<eta>)"
    using step N\<eta>
    by (meson Infinitesimal_HFinite_mult2 Infinitesimal_approx_minus Infinitesimal_hnorm_iff
      Infinitesimal_star_of_mult2 approx_star_of_HFinite hnorm_le_Infinitesimal)

  txt \<open>The times: \<open>N \<delta> \<approx> s a\<close> and \<open>N \<eta> \<approx> s\<close>.\<close>
  have "?N * \<delta> = ?N * \<eta> * (\<delta> / \<eta>)"
    using \<eta>(1) by simp
  then have "( *f* M) (?N * \<delta>) \<approx> star_of (M (s * a))"
    using approx_mult_star_of[OF N\<eta> a(2)] \<delta>(1) a(1) s
    by (intro approx_continuous_on[OF M(1)]) (simp_all add: starset_atLeast)
  moreover have "( *f* E) (?N * \<eta>) \<approx> star_of (E s)"
    using N\<eta> \<eta>(1) s
    by (intro approx_continuous_on[OF E(1)]) (simp_all add: starset_atLeast less_imp_le)
  ultimately show ?thesis
    using close by (metis approx_trans3 star_of_approx_iff)
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
    using epsilon_gt_zero
    by (intro approx_continuous_on[OF cont]) (simp_all add: starset_atLeast less_imp_le)
  moreover have "\<And>h. ( *f* \<eta>) h = h + hnorm (( *f* M) h - 1)"
    unfolding \<eta>_def by transfer (rule refl)
  ultimately have \<eta>0: "?\<eta> \<in> Infinitesimal"
    by (simp add: M0 approx_def Infinitesimal_add Infinitesimal_hnorm_iff)

  txt \<open>On that scale, the change has a standard part \<open>B\<close>, and the time is close to \<open>a\<close>.\<close>
  have scale: "\<forall>h>0. h \<le> \<eta> h \<and> 0 < \<eta> h \<and> h / \<eta> h + norm (Q h) = 1"
    by (auto simp: \<eta>_def Q_def divide_simps add_pos_nonneg add_nonneg_eq_0_iff)
  then have "\<forall>h>0. h \<le> ( *f* \<eta>) h \<and> 0 < ( *f* \<eta>) h \<and> h / ( *f* \<eta>) h + hnorm (( *f* Q) h) = 1"
    by transfer
  then have \<eta>: "\<epsilon> \<le> ?\<eta>" "0 < ?\<eta>" and sum: "\<epsilon> / ?\<eta> = 1 - hnorm ?Q"
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
  have Econt: "continuous_on {0..} E"
    by (intro continuous_at_imp_continuous_on ballI has_vector_derivative_continuous[OF Ederiv])
  have "(DE \<longlongrightarrow> B) (at 0)"
    using Ederiv[of 0] unfolding has_vector_derivative_within_1D by (simp add: DE_def E0)
  then have DE: "( *f* DE) ?\<eta> \<approx> star_of B"
    using \<eta>(2) \<eta>0 by (auto dest!: LIM_NSLIM simp: NSLIM_def mem_infmal_iff)
  have "\<forall>h>0. norm (M h - E (\<eta> h)) / \<eta> h = norm (Q h - DE (\<eta> h))"
    using scale by (simp add: Q_def DE_def abs_of_pos divide_inverse flip: scaleR_diff_right)
  then have "\<forall>h>0. hnorm (( *f* M) h - ( *f* E) (( *f* \<eta>) h)) / ( *f* \<eta>) h
      = hnorm (( *f* Q) h - ( *f* DE) (( *f* \<eta>) h))"
    by transfer
  then have step: "hnorm (( *f* M) \<epsilon> - ( *f* E) ?\<eta>) / ?\<eta> \<in> Infinitesimal"
    using approx_hnorm[OF approx_diff[OF B(1) DE]] epsilon_gt_zero by (simp add: mem_infmal_iff)

  txt \<open>Euler's step, and the semigroup is not infinitely fast.\<close>
  have main: "M (s * a) = E s" if "0 \<le> s" for s
    using epsilon_gt_zero
    by (intro euler_step[OF cont M0 add Econt E0 Eadd _ \<eta> \<eta>0 a step that]) simp_all
  have "a \<noteq> 0"
  proof
    assume "a = 0"
    then have "\<forall>u>0. DE u = 0"
      using main M0 by (simp add: DE_def)
    then have "\<forall>u>0. ( *f* DE) u = 0"
      by transfer
    then show False
      using DE \<eta>(2) \<open>a = 0\<close> by (simp add: a_def)
  qed
  then have "M t = exp (t *\<^sub>R (B /\<^sub>R a))" if "0 \<le> t" for t
    using main[of "t / a"] that a(1) by (simp add: E_def flip: divide_inverse)
  then show ?thesis
    by blast
qed

end
