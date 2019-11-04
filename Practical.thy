theory Practical
imports Main
begin

(***************************First-order logic*************************************)

(*1 mark*)
lemma "A∨A ⟶ A"
  apply (rule impI)
  apply (erule disjE)
   apply assumption+
  done


(*1 mark*)
lemma "(P⟶R)⟶(¬P∨R)"
  apply (rule impI)
  apply (rule classical)
  apply (rule disjI1)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply (erule impE)
   apply assumption
  apply assumption
  done

(*1 mark*)
lemma "(P∧Q⟶R)⟶P⟶Q⟶R"
  apply (rule impI)+
  apply (erule impE)
   apply (rule conjI)
    apply assumption+
  done

(*3 marks*)
lemma "¬¬P ∨ ¬P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2) 
  apply assumption
  done

(*4 marks*)
lemma "(P∨R)⟷(¬(¬P∧ ¬R))"
  apply (rule iffI)
   apply (erule disjE)
    apply (rule notI)
  apply (erule conjE)
    apply (erule notE)
    apply assumption
   apply (rule notI)
   apply (erule conjE)
   apply (erule notE)+
   apply assumption

 apply (rule classical)
   apply (erule notE)
   apply (rule conjI)
   apply (rule notI)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule notI)
   apply (erule notE)
   apply (rule disjI2)
  apply assumption
  done

lemma not_not_p_is_p: "¬¬P ⟹ P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

(*1 mark*)
lemma "(∀ x . F x ⟶ G x ) ⟶ ¬ (∃ x . F x ∧ ¬ G x )"
  apply (rule impI)
  apply (rule classical)
  apply (drule not_not_p_is_p)
  apply (erule exE)
  apply (erule allE)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

(*1 mark*)
lemma "(∀ x y. R x y) ⟶ (∀ x . R x x )"
  apply (rule impI)
  apply (rule allI)
  apply (erule allE)+
  apply assumption
  done

(*3 marks*)
lemma "(∀x. P x)∨(∃x.¬P x)"
  apply (rule classical)
  apply (rule disjI1 notI)+
  apply (rule allI)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  apply (rule exI)
  apply assumption
  done


(*3 marks*)
lemma "(∀x. ¬ (P x ⟶ Q x)) ⟶ ¬(∃x. ¬P x ∧ Q x)"
  apply (rule impI)
  apply (rule classical)
  apply (drule not_not_p_is_p)
  apply (erule exE)
  apply (erule allE)
  apply (erule conjE)
  apply (erule notE)
  apply (rule impI)
  apply assumption
  done


(*3 marks*)
lemma "∃Bob. (drunk Bob ⟶ (∀y. drunk y))"
  apply (rule classical)
  apply (rule exI)
  apply (rule impI)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule exI)
  apply (rule impI)
  apply (erule notE)
  apply assumption
  done


(*4 marks*)
lemma "¬ (∃ barber . man barber ∧ (∀ x . man x ∧ ¬shaves x x ⟷ shaves barber x ))"
apply (rule notI)
apply (erule exE)
apply (erule conjE)
apply (erule allE)
apply (erule iffE)
apply (erule impE)
apply (rule conjI)
apply assumption
apply (rule notI)
apply (erule impE, assumption, erule conjE, erule notE, assumption)+
done
  

locale incidence =
  fixes incidence_points_on_sections :: "'point ⇒ 'section ⇒ bool" (infix " ι⇩p⇩o⇩i⇩n⇩t " 80)
  fixes region_to_section :: "'region ⇒ 'section" 
  assumes section_nonempty: "∀s. ∃p. p ι⇩p⇩o⇩i⇩n⇩t s" 
(*Write here your axiom stating that every section has 
                                            a point incident to it*) (*2 marks*)
  and section_uniqueness: "∀s l. (∀p. p ι⇩p⇩o⇩i⇩n⇩t s ⟷ p ι⇩p⇩o⇩i⇩n⇩t l) ⟶ s = l" 
(*  and section_uniqueness_meta: "⟦a ι⇩p⇩o⇩i⇩n⇩t s ⟷ a ι⇩p⇩o⇩i⇩n⇩t l⟧ ⟹ s = l" *)
(*Write here your axiom stating that ANY two sections are the same
                                      if ANY of the same points are incident to each*) (*2 marks*)
begin

definition isPartOf ::"'section ⇒ 'section ⇒ bool" (infix "isPartOf" 80) where 
"a isPartOf b = (∀p. p ι⇩p⇩o⇩i⇩n⇩t a ⟶ p ι⇩p⇩o⇩i⇩n⇩t b)"
(*write your formalisation of definition D1 here*) (*1 mark*)

definition inclusion ::"'region ⇒ 'section ⇒ bool"(infix "isIncludedIn" 80) where
(*write your formalisation of definition D2 here*) (*1 mark*)
"a isIncludedIn b = (region_to_section a) isPartOf b"

definition overlaps ::"'region ⇒ 'section ⇒ bool"(infix "overlaps" 80) where
(*write your formalisation of definition D3 here*) (*1 mark*)
"a overlaps b = (∃p. p ι⇩p⇩o⇩i⇩n⇩t (region_to_section a) ∧ p ι⇩p⇩o⇩i⇩n⇩t b)"

lemma region_overlaps_itself: "R overlaps (region_to_section R)"
(*Write your structured proof here*) (*2 marks*)
proof (unfold overlaps_def)
  from section_nonempty obtain p where "p ι⇩p⇩o⇩i⇩n⇩t region_to_section R" by blast
  then show "∃p. p  ι⇩p⇩o⇩i⇩n⇩t region_to_section R ∧ p  ι⇩p⇩o⇩i⇩n⇩t region_to_section R"
    by blast
qed  

(*Formalise and prove that isPartOf is reflexive, transitive and antisymmetric*) (*3 marks*)
lemma isPartOf_reflexive: "a isPartOf a"
  by (simp add: isPartOf_def)

lemma ipo_ref: 
  assumes "∀p. p ι⇩p⇩o⇩i⇩n⇩t a"
  shows "a isPartOf a" 
proof - 
  show "a isPartOf a"
    by (simp add: isPartOf_def)
qed

lemma isPartOf_transitive:
  assumes ab: "a isPartOf b" and bc: "b isPartOf c"
  shows ac: "a isPartOf c"
proof (unfold isPartOf_def)
show "∀p. p  ι⇩p⇩o⇩i⇩n⇩t  a ⟶ p  ι⇩p⇩o⇩i⇩n⇩t  c"
    using ab bc isPartOf_def by blast
qed
  
lemma isPartOf_antisymmetric:
  assumes ab: "a isPartOf b" and ba: "b isPartOf a"
  shows "a = b"
proof -
  show "a = b"
    using ab ba isPartOf_def section_uniqueness by blast
qed


end


locale section_bundles =  incidence incidence_points_on_sections region_to_section 
  for  incidence_points_on_sections :: "'point ⇒ 'section ⇒ bool" 
  and region_to_section :: "'region ⇒ 'section" +
  fixes crossing :: "'region ⇒ 'section ⇒ bool" (infix "crosses" 80)
  and incidence_sections_on_bundles :: "'section ⇒ 'bundle ⇒ bool" (infix "ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n" 80) 
 assumes SC1:"∀s r. r crosses s ⟶ r overlaps s" (*Write your formalisation of Axiom SC1 here*) (*1 mark*)
 and SI1: "∀a b. (∀s. s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n a ⟷ s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b) ⟶ a = b" (*Write your formalisation of Axiom SI1 here*)     (*1 mark*)
begin

definition atLeastAsRestrictiveAs :: "'section ⇒ 'bundle ⇒ 'section ⇒ bool" where 
(*Write your formalisation of atLeastAsRestrictiveAs here*) (*1 mark*)
"atLeastAsRestrictiveAs s b s' = (s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ s isPartOf s')"

notation 
  atLeastAsRestrictiveAs ("_ ≤⇩_ _" [80, 80, 80] 80)


(*Formalise and prove that atLeastAsRestrictiveAs is reflexive, transitive and antisymmetric*) (*2 marks*)

(*Kulik and Eschenbach say 'The relation ≥ is reflexive, transitive and antisymmetric for a given 
sector bundle.' So, do they mean, given that the sections under consideration are in the bundle?
This is what we assume for reflexivity.*)
lemma atLeastAsRestrictiveAs_reflexive: 
  assumes "s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b"  shows "s ≤⇩b s" (* given: DO NOT REMOVE! *)
proof (unfold atLeastAsRestrictiveAs_def)
  show "s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ s isPartOf s"
    by (simp add: assms isPartOf_reflexive)
qed

lemma atLeastAsRestrictiveAs_transitive: 
(*Formalise and prove that atLeastAsRestrictiveAs is transitive*)
  assumes xy: "x ≤⇩b y" and yz: "y ≤⇩b z" 
  shows "x ≤⇩b z"
proof (unfold atLeastAsRestrictiveAs_def)
  show "x ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ z ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ x isPartOf z"
    using atLeastAsRestrictiveAs_def isPartOf_transitive xy yz by blast
qed

lemma atLeastAsRestrictiveAs_antisymmetric: 
(*Formalise and prove that atLeastAsRestrictiveAs is antisymmetric*)
  assumes xy: "x ≤⇩b y" and yx: "y ≤⇩b x" 
  shows "x = y"
proof - 
  show "x = y"
    using atLeastAsRestrictiveAs_def isPartOf_antisymmetric xy yx by auto
qed


end

locale comparison = section_bundles incidence_points_on_sections region_to_section 
 crossing incidence_sections_on_bundles
  for  incidence_points_on_sections :: "'point ⇒ 'section ⇒ bool" (infix "ι⇩p⇩o⇩i⇩n⇩t" 80) 
  and region_to_section :: "'region ⇒ 'section" 
  and crossing :: "'region ⇒ 'section ⇒ bool" (infix "crosses" 80) 
  and incidence_sections_on_bundles :: "'section ⇒ 'bundle ⇒ bool" (infix "ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n" 80)+
assumes SB2: "∀b s s'. (s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b) ⟶ (s ≤⇩b s' ∨ s' ≤⇩b s)"
    (*Write your formalisation of Axiom SB2 here*) (*1 mark*)

begin

lemma T1:(*Write your formalisation and proof of Theorem T1 here*) (*1 mark*)
  assumes r_overlaps_s: "r overlaps s" 
  shows "∀s'. (s ≤⇩b s' ⟶ r overlaps s')"
proof -
  show  "∀s'. (s ≤⇩b s' ⟶ r overlaps s')"
    using atLeastAsRestrictiveAs_def isPartOf_def overlaps_def r_overlaps_s by auto 
qed

lemma T2: (*Write your formalisation and proof of Theorem T2 here*) (*1 mark*)
  assumes r_isincludedin_s: "r isIncludedIn s"
  shows "∀s'. (s ≤⇩b s' ⟶ r isIncludedIn s')"
proof - 
  show "∀s'. s ≤⇩b s' ⟶ r isIncludedIn s'"
    using atLeastAsRestrictiveAs_def inclusion_def isPartOf_transitive r_isincludedin_s by blast
qed

definition isCore (infix "isCoreOf" 80) where
"s isCoreOf b = (s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ (∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ s ≤⇩b s'))"

(*Write your definition of hull here*) (*1 mark*)
definition isHull (infix "isHullOf" 80) where
"s isHullOf b = (s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ (∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ s' ≤⇩b s))"

end

locale crossing_sector = comparison incidence_points_on_sections 
          region_to_section crossing incidence_sections_on_bundles
          for incidence_points_on_sections :: "'point ⇒ 'section ⇒ bool" (infix "ι⇩p⇩o⇩i⇩n⇩t" 80) 
and region_to_section :: "'region ⇒ 'section" 
and crossing :: "'region ⇒ 'section ⇒ bool" (infix "crosses" 80)  
and incidence_sections_on_bundles :: "'section ⇒ 'bundle ⇒ bool" (infix "ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n" 80) +
assumes SC2: "∀b S R. (R crosses S ⟶ (∀S. (S' ≤⇩b S ⟶ R crosses S')))"
(*Write your formalisation of Axiom SC2 here*) (*1 mark*)
begin


lemma overlaps_core: (*Write your formalisation and structured proof of the remark `If a region 
overlaps the core of a section bundle then it overlaps every section of the section bundle'*) 
(*4 marks*)
  assumes r_overlaps_s: "r overlaps s" and s_isCoreOf_b: "s isCoreOf b"
  shows "∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ r overlaps s'"
proof (rule allI, rule impI)
  fix s'
  assume s_incidence_b: "s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b" 
  have s_isC_b: "s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ (∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ s ≤⇩b s')"
    using isCore_def s_isCoreOf_b by blast 
  have s_atleastasrestrictiveas_s': "s ≤⇩b s'"
    by (simp add: s_incidence_b s_isC_b)
  show "r overlaps s'"
    using T1 r_overlaps_s s_atleastasrestrictiveas_s' by blast 
qed


lemma crosses_hull: (*Write your formalisation and structured proof of the remark `If a region 
crosses the hull of a section bundle then it crosses every sector of the section bundle'*) 
(*4 marks*)
  assumes r_crosses_s: "r crosses s" and s_isHullOf_b: "s isHullOf b"
  shows "∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ r crosses s'"
proof (rule allI, rule impI)
  fix s'
  assume s'_incidence_b: "s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b" 
  have s_isH_b: "s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ (∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ s' ≤⇩b s)"
    using isHull_def s_isHullOf_b by blast
  have s'_atleastasrestrictiveas_s: "s' ≤⇩b s"
    by (simp add: s'_incidence_b s_isH_b)
  show "r crosses s'"
    using SC2 r_crosses_s s'_atleastasrestrictiveas_s by blast
qed


lemma not_overlap_hull:  (*Write your formalisation and structured proof of the remark `If a region 
does not overlap the hull of a section bundle, it does not overlap any of its sections'*) 
(*4 marks*)
  assumes r_not_overlaps_s: "¬(r overlaps s)" and s_isHullOf_b: "s isHullOf b"
  shows "∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ ¬(r overlaps s')"
proof (rule allI, rule impI)
  fix s'
  assume s'_incidence_b: "s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b" 
  have s_isH_b: "s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ (∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ s' ≤⇩b s)"
    using isHull_def s_isHullOf_b by blast
  have s'_atleastasrestrictiveas_s: "s' ≤⇩b s"
    by (simp add: s'_incidence_b s_isH_b)
  show "¬(r overlaps s')"
    using T1 r_not_overlaps_s s'_atleastasrestrictiveas_s by blast
qed

definition overlapsAsMuchAs :: "'region ⇒ 'bundle ⇒ 'region ⇒ bool"  where 
"overlapsAsMuchAs R b R' == (∀s. s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ R' overlaps s ⟶ R overlaps s)"

notation 
  overlapsAsMuchAs ("_ ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩_ _" [80, 80, 80] 80)

definition eq_overlapsAsMuchAs :: "'region ⇒ 'bundle ⇒ 'region ⇒ bool"  where 
"eq_overlapsAsMuchAs R b R' == R ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ∧ R' ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R"

notation 
  eq_overlapsAsMuchAs ("_ ≅⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩_ _" [80, 80, 80] 80)

abbreviation
rev_overlapsAsMuchAs :: "'region ⇒ 'bundle ⇒ 'region ⇒ bool"  ("_ ≤⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩_ _" [80, 80, 80] 80)
where"rev_overlapsAsMuchAs R b R' == overlapsAsMuchAs R' b R"

definition more_overlapsAsMuchAs :: "'region ⇒ 'bundle ⇒ 'region ⇒ bool"  where 
"more_overlapsAsMuchAs R b R' == R ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ∧ ¬(R' ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R)"

notation 
  more_overlapsAsMuchAs ("_ >⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩_ _" [80, 80, 80] 80)

abbreviation
less_overlapsAsMuchAs :: "'region ⇒ 'bundle ⇒ 'region ⇒ bool"  ("_ <⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩_ _" [80, 80, 80] 80)
where"less_overlapsAsMuchAs R b R' == more_overlapsAsMuchAs R' b R"

(*Formalise and prove that overlapsAsMuchAs is reflexive and transitive*) (*2 marks*)

lemma overlapsAsMuchAs_reflexive:
(*Write your formalisation and proof that overlapsAsMuchAs is reflexive here*) 
  assumes "(region_to_section R) ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b"  
  shows "R ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R"
proof -
  show "R ≤⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R"
    by (simp add: overlapsAsMuchAs_def)
qed


lemma overlapsAsMuchAs_transitive:
(*Write your formalisation and proof that overlapsAsMuchAs is transitive here*)
  assumes xy: "X ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b Y" and yz: "Y ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b Z"
  shows xz: "X ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b Z"
proof - 
  show "X ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b Z"
    using overlapsAsMuchAs_def xy yz by auto
qed

(* SB2: "∀b s s'. (s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b) ⟶ (s ≤⇩b s' ∨ s' ≤⇩b s)" *)

(* lemma T1: 
  assumes r_overlaps_s: "r overlaps s" 
  shows "∀s'. (s ≤⇩b s' ⟶ r overlaps s')" *)

(*Write your formalisation and structured proof of Theorem T3 here. You must attempt to 
formalise Kulik et al.'s reasoning*) (*11 marks*)
lemma T3: "∀b R R'.  R <⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ⟷ (∃s. s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ∧ R overlaps s ∧ ¬( R' overlaps s))"
proof (rule allI)

(* DIRECTION <-- *)
  fix s 
  assume s_inbundle_b: "s ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b" and r_overlaps_s: "R overlaps s" and r'_notoverlaps_s: "¬( R' overlaps s)"
  have s_s'_isPartOf: "∀s'. s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b ⟶ s isPartOf s' ∨ s' isPartOf s"
    using SB2 atLeastAsRestrictiveAs_def s_inbundle_b by auto

 (* assume s isPartOf s' *)
  assume s'_inbundle_b: "s' ι⇩s⇩e⇩c⇩t⇩i⇩o⇩n b" and s_isPartOf_s': "s isPartOf s'"
  have s_atleastasrestrictiveas_s': "s ≤⇩b s'"
    by (simp add: atLeastAsRestrictiveAs_def s'_inbundle_b s_inbundle_b s_isPartOf_s')
  have rest_implies_r_o_s': "∀s'. (s ≤⇩b s' ⟶ R overlaps s')"
    using T1 r_overlaps_s by blast
  (* then have "R overlaps s'" *) 
  have r_overlaps_s': "R overlaps s'"
    by (simp add: rest_implies_r_o_s' s_atleastasrestrictiveas_s')

  (* assume s' isPartOf s *)
  assume s'_isPartOf_s: "s' isPartOf s" 
  have s'_atleastasrestrictiveas_s: "s' ≤⇩b s"
    by (simp add: atLeastAsRestrictiveAs_def s'_inbundle_b s'_isPartOf_s s_inbundle_b)
  (* then have "¬(R' overlaps s')" *) 
  have r'_notoverlaps_s': "¬(R' overlaps s')"
    using T1 r'_notoverlaps_s s'_atleastasrestrictiveas_s by blast

  (* from previous, have "R ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'" *)
  from r_overlaps_s' r'_notoverlaps_s' have r_oama_r': "R ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'"
    using SB2 T1 overlapsAsMuchAs_def s'_inbundle_b by blast

  (* therefore from r'_notoverlaps_s we have "R >⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'" *)
  from r'_notoverlaps_s have "R >⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'"
    using more_overlapsAsMuchAs_def overlapsAsMuchAs_def r'_notoverlaps_s' r_oama_r' r_overlaps_s' s'_inbundle_b by blast

  oops






(*In under 200 words, compare and contrast the mechanical proof that you produced with the 
pen-and-paper proof by Kulik et al.\. In particular, indicate any reasoning, proof parts, and/or 
useful lemmas that you had to make explicit during the mechanisation but may have been glossed over
 or assumed by the pen-and-paper proof. Also highlight any inaccuracies in their language or 
notation. Note any parts where you had to diverge from their reasoning, and why.
Write your answer in a comment here.*) (*4 marks*)

(*Write your formalisation and proof of Theorem T4 here*) (*1 mark*)
lemma T4: "∀b R R'.  R <⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ∨ R ≅⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ∨ R <⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'"
proof - 
  show "∀b R R'.  R <⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ∨ R ≅⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ∨ R <⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'"
    using T3 eq_overlapsAsMuchAs_def more_overlapsAsMuchAs_def overlapsAsMuchAs_def by auto 
qed 

(*Write your formalisation and structured proof of Theorem T5 here. You must show it follows from T4*) (*3 marks*)
(* lemma T5: "∀b R R'.  R ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ∨ R ≤⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'"
proof - 
  show "∀b R R'. R' ≤⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R ∨ R ≤⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'"
    using T4 eq_overlapsAsMuchAs_def more_overlapsAsMuchAs_def by blast
qed *) 
lemma T5: "∀b R R'.  R ≥⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R' ∨ R ≤⇩o⇩v⇩e⇩r⇩l⇩a⇩p⇩s ⇩b R'"
proof (unfold overlapsAsMuchAs_def, rule allI)
  oops
  


(********************Challenge problem****************************************)

(*Write your definition of `crosses or is included in as much as' here*) (*2 marks*)
(*If a region crosses a section or is included in a section, R ci S*)
definition crossesIncludedInAsMuchAs :: "'region ⇒ 'section ⇒ bool" (infix "ci" 80) where
"R ci S = (R crosses S ∨ R isIncludedIn S)"

(*Write your definition of `belongs as much as here: definition D8 in the paper.*) (*2 marks*)
definition belongsAsMuchAs 

(*Formalise and write structured proofs of Theorems T6-T8 for both crossesIncludedInAsMuchAs and
belongsAsMuchAs*) (*14 marks*)

lemma T6_crossesIncludedInAsMuchAs:

lemma T6_belongsAsMuchAs:

lemma T7_crossesIncludedInAsMuchAs:

lemma T7_belongsAsMuchAs:

lemma T8_crossesIncludedInAsMuchAs:

lemma T8_belongsAsMuchAs:

end

end
