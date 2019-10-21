theory Practical
imports Main
begin

(***************************First-order logic*************************************)

(*1 mark*)
lemma "A\<or>A \<longrightarrow> A"
  apply (rule impI)
  apply (erule disjE)
   apply assumption+
  done

(*1 mark*)
lemma "(P\<longrightarrow>R)\<longrightarrow>(\<not>P\<or>R)"
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
lemma "(P\<and>Q\<longrightarrow>R)\<longrightarrow>P\<longrightarrow>Q\<longrightarrow>R"
  apply (rule impI)+
  apply (erule impE)
   apply (rule conjI)
  apply assumption+

(*3 marks*)
lemma "\<not>\<not>P \<or> \<not>P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2) 
  apply assumption
  done

(*4 marks*)
lemma "(P\<or>R)\<longleftrightarrow>(\<not>(\<not>P\<and> \<not>R))"
  apply (rule iffI)
   apply (erule disjE)
    apply (rule notI)
  apply (erule conjE)
    apply (erule notE)
    apply assumption
   apply (rule notI)
   apply (erule conjE)
   apply (erule notE)
   apply (erule notE)
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

lemma not_not_p_is_p: "\<not>\<not>P \<Longrightarrow> P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

(*1 mark*)
lemma "(\<forall> x . F x \<longrightarrow> G x ) \<longrightarrow> \<not> (\<exists> x . F x \<and> \<not> G x )"
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
lemma "(\<forall> x y. R x y) \<longrightarrow> (\<forall> x . R x x )"
  apply (rule impI)
  apply (rule allI)
  apply (erule allE)+
  apply assumption
  done

(*3 marks*)
lemma "(\<forall>x. P x)\<or>(\<exists>x.\<not>P x)"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule allI)
  apply (rule classical)
  apply (erule notE)
  oops

(*3 marks*)
lemma "(\<forall>x. \<not> (P x \<longrightarrow> Q x)) \<longrightarrow> \<not>(\<exists>x. \<not>P x \<and> Q x)"
  apply (rule impI)
  apply (rule classical)
  apply (drule not_not_p_is_p)
  apply (erule exE)
  apply (erule allE)
  apply (erule conjE)
  apply (erule notE)
  apply (rule impI)
  apply assumption


(*3 marks*)
lemma "\<exists>Bob. (drunk Bob \<longrightarrow> (\<forall>y. drunk y))"
  apply (cut_tac P = "(\<forall>y. drunk y)" in excluded_middle)
  apply (erule disjE)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule exI)
  apply (rule impI)
  apply (erule notE)
  apply assumption
  apply (rule exI)
  apply (rule impI)
  apply assumption
  done


(*4 marks*)
lemma "\<not> (\<exists> barber . man barber \<and> (\<forall> x . man x \<and> \<not>shaves x x \<longleftrightarrow> shaves barber x ))"
  oops

locale incidence =
  fixes incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix " \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t " 80)
  fixes region_to_section :: "'region \<Rightarrow> 'section" 
  assumes section_nonempty: (*Write here your axiom stating that every section has 
                                            a point incident to it*) (*2 marks*)
  and section_uniqueness: (*Write here your axiom stating that two sections are the same
                                      if the same points are incident to each*) (*2 marks*)
begin

definition isPartOf ::"'section \<Rightarrow> 'section \<Rightarrow> bool" (infix "isPartOf" 80) where 
(*write your formalisation of definition D1 here*) (*1 mark*)

definition inclusion ::"'region \<Rightarrow> 'section \<Rightarrow> bool"(infix "isIncludedIn" 80) where
(*write your formalisation of definition D2 here*) (*1 mark*)

definition overlaps ::"'region \<Rightarrow> 'section \<Rightarrow> bool"(infix "overlaps" 80) where
(*write your formalisation of definition D3 here*) (*1 mark*)

lemma region_overlaps_itself: "R overlaps (region_to_section R)"
(*Write your structured proof here*) (*2 marks*)
  oops

(*Formalise and prove that isPartOf is reflexive, transitive and antisymmetric*) (*3 marks*)
lemma isPartOf_reflexive: 
(*Formalise and prove that isPartOf is reflexive here*)
  oops

lemma isPartOf_transitive: 
(*Formalise and prove that isPartOf is transitive here*)
  oops

lemma isPartOf_antisymmetric: 
(*Formalise and prove that isPartOf is antisymmetric here*)
  oops

 
end


locale section_bundles =  incidence incidence_points_on_sections region_to_section 
  for  incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" 
  and region_to_section :: "'region \<Rightarrow> 'section" +
  fixes crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" 
  and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80) 
 assumes SC1: (*Write your formalisation of Axiom SC1 here*) (*1 mark*)
 and SI1: (*Write your formalisation of Axiom SI1 here*)     (*1 mark*)
begin

definition atLeastAsRestrictiveAs :: "'section \<Rightarrow> 'bundle \<Rightarrow> 'section \<Rightarrow> bool" where 
(*Write your formalisation of atLeastAsRestrictiveAs here*) (*1 mark*)

notation 
  atLeastAsRestrictiveAs ("_ \<le>\<^sub>_ _" [80, 80, 80] 80)


(*Formalise and prove that isPartOf is reflexive, transitive and antisymmetric*) (*2 marks*)

(*Kulik and Eschenbach say 'The relation \<ge> is reflexive, transitive and antisymmetric for a given 
sector bundle.' So, do they mean, given that the sections under consideration are in the bundle?
This is what we assume for reflexivity.*)
lemma atLeastAsRestrictiveAs_reflexive: 
  assumes "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"  shows "s \<le>\<^sub>b s"
(*Add your proof here*)
  oops

lemma atLeastAsRestrictiveAs_transitive: 
(*Formalise and prove that atLeastAsRestrictiveAs is transitive*)
  oops

lemma atLeastAsRestrictiveAs_antisymmetric: 
(*Formalise and prove that atLeastAsRestrictiveAs is antisymmetric*))
  oops

end

locale comparison = section_bundles incidence_points_on_sections region_to_section 
 crossing incidence_sections_on_bundles
  for  incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix "\<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t" 80) 
  and region_to_section :: "'region \<Rightarrow> 'section" 
  and crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" (infix "crosses" 80) 
  and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80)+
assumes SB2:(*Write your formalisation of Axiom SB2 here*) (*1 mark*)
begin

lemma T1:(*Write your formalisation and proof of Theorem T1 here*) (*1 mark*)

lemma T2:(*Write your formalisation and proof of Theorem T2 here*) (*1 mark*)

definition isCore (infix "isCoreOf" 80) where
"s isCoreOf b = (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<forall>s'. s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s \<le>\<^sub>b s'))"

definition (*Write your definition of hull here*) (*1 mark*)


end

locale crossing_sector = comparison incidence_points_on_sections 
          region_to_section crossing incidence_sections_on_bundles
          for incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix "\<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t" 80) 
and region_to_section :: "'region \<Rightarrow> 'section" 
and crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" (infix "crosses" 80)  
and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80) +
assumes SC2: (*Write your formalisation of Axiom SC2 here*) (*1 mark*)
begin


lemma overlaps_core: (*Write your formalisation and structured proof of the remark `If a region 
overlaps the core of a section bundle then it overlaps every section of the section bundle'*) 
(*4 marks*)

lemma crosses_hull: (*Write your formalisation and structured proof of the remark `If a region 
crosses the hull of a section bundle then it crosses every sector of the section bundle'*) 
(*4 marks*)

lemma not_overlap_hull:  (*Write your formalisation and structured proof of the remark `If a region 
does not overlap the hull of a section bundle, it does not overlap any of its sections'*) 
(*4 marks*)

definition overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"overlapsAsMuchAs R b R' == (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' overlaps s \<longrightarrow> R overlaps s)"

notation 
  overlapsAsMuchAs ("_ \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

definition eq_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"eq_overlapsAsMuchAs R b R' == R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R"

notation 
  eq_overlapsAsMuchAs ("_ \<cong>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

abbreviation
rev_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  ("_ \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)
where"rev_overlapsAsMuchAs R b R' == overlapsAsMuchAs R' b R"

definition more_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"more_overlapsAsMuchAs R b R' == R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> \<not>(R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R)"

notation 
  more_overlapsAsMuchAs ("_ >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

abbreviation
less_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  ("_ <\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)
where"less_overlapsAsMuchAs R b R' == more_overlapsAsMuchAs R' b R"

(*Formalise and prove that overlapsAsMuchAs is reflexive and transitive*) (*2 marks*)

lemma overlapsAsMuchAs_reflexive:
(*Write your formalisation and proof that overlapsAsMuchAs is reflexive here*) 

lemma overlapsAsMuchAs_transitive:
(*Write your formalisation and proof that overlapsAsMuchAs is transitive here*)

lemma T4: (*Write your formalisation and proof of Theorem T4 here*) (*1 mark*)

lemma T5: (*Write your formalisation and structured proof of Theorem T5 here. 
You must show it follows from T4*) (*3 marks*)


lemma T3: (*Write your formalisation and structured proof of Theorem T3 here. You must attempt to 
formalise Kulik et al.'s reasoning*) (*11 marks*)

(*In under 200 words, compare and contrast the mechanical proof that you produced with the 
pen-and-paper proof by Kulik et al.\. In particular, indicate any reasoning, proof parts, and/or 
useful lemmas that you had to make explicit during the mechanisation but may have been glossed over
 or assumed by the pen-and-paper proof. Also highlight any inaccuracies in their language or 
notation. Note any parts where you had to diverge from their reasoning, and why.
Write your answer in a comment here.*) (*4 marks*)

(********************Challenge problem****************************************)

definition crossesIncludedInAsMuchAs (*Write your definition of `crosses or is included in as much
as' here*) (*2 marks*)

definition belongsAsMuchAs (*Write your definition of `belongs as much as here: definition D8 in
the paper.*) (*2 marks*)

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