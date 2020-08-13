; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-fun f_str (RDFValue) RDFValue)
(declare-fun f_xsd_string (RDFValue) RDFValue)
(declare-fun f_datatype (RDFValue) RDFValue)
(declare-fun f_lcase (RDFValue) RDFValue)
(declare-fun f_round (RDFValue) RDFValue)
(declare-fun f_abs (RDFValue) RDFValue)
(declare-fun f_isliteral (RDFValue) Bool)
(declare-fun f_isuri (RDFValue) Bool)
(declare-fun f_contains (RDFValue RDFValue) Bool)
(declare-fun f_regex (RDFValue RDFValue) Bool)
(declare-fun f_add (RDFValue RDFValue) RDFValue)
(declare-fun f_sub (RDFValue RDFValue) RDFValue)
(declare-fun f_mul (RDFValue RDFValue) RDFValue)
(declare-fun f_div (RDFValue RDFValue) RDFValue)
(declare-fun f_lt (RDFValue RDFValue) Bool)
(declare-fun f_gt (RDFValue RDFValue) Bool)
(declare-fun f_leq (RDFValue RDFValue) Bool)
(declare-fun f_geq (RDFValue RDFValue) Bool)
(declare-fun f_bound (RDFValue) Bool)
(declare-const <default_graph> RDFValue)
(assert (forall ((s RDFValue)(p RDFValue)(o RDFValue)(g RDFValue)) (=> (P s p o g) (P s p o <default_graph>))))

; ------------ IRIs ---------------------------------
(declare-const	<a>	RDFValue)
(declare-const	<p1_GraduateStudent>	RDFValue)
(declare-const	<p1_Student>	RDFValue)
(declare-const	<p1_UndergradStudent>	RDFValue)
(declare-const	<p1_courseName>	RDFValue)
(declare-const	<p1_sex>	RDFValue)
(declare-const	<p1_takesCourse>	RDFValue)
(declare-const	<p1_telephone>	RDFValue)
(declare-const	<p2_subClassOf>	RDFValue)

; ------------ Literals -----------------------------
(declare-const	<l_0>	RDFValue)
(declare-const	<l_1>	RDFValue)

; ------------ Schema -------------------------------
(assert 
	(and 
		(forall ((x RDFValue)(g RDFValue)) (=> (P x <a> <p1_GraduateStudent> g) (P x <a> <p1_Student> g)))
		(forall ((x RDFValue)(g RDFValue)) (=> (P x <a> <p1_UndergradStudent> g) (P x <a> <p1_Student> g)))
	)
)

; ------------ Variables ----------------------------
(declare-const	<v3_tel>	RDFValue)
(declare-const	<v3_x>	RDFValue)
(declare-const	<v3_y>	RDFValue)

; ------------ Assumption ---------------------------
(assert 
	(and 
		(or (P <v3_x> <a> <p1_GraduateStudent> <default_graph>) )
		(or (P <v3_x> <p1_takesCourse> <v3_y> <default_graph>) )
		(or (P <v3_x> <p1_telephone> <v3_tel> <default_graph>) )
		(or (P <v3_x> <p1_sex> <l_0> <default_graph>) )
		(or (P <v3_y> <p1_courseName> <l_1> <default_graph>) )
	)
)

; ------------ Conjecture ---------------------------
(assert (not (exists ((<v2_tel> RDFValue)(<v2_x> RDFValue)(<v2_y> RDFValue)) 
	(and 
		(or (P <v2_x> <a> <p1_Student> <default_graph>) )
		(or (P <v2_x> <p1_takesCourse> <v2_y> <default_graph>) )
		(or (P <v2_x> <p1_telephone> <v2_tel> <default_graph>) )
		(or (P <v2_x> <p1_sex> <l_0> <default_graph>) )
		(or (P <v2_y> <p1_courseName> <l_1> <default_graph>) )
		(and (= <v2_x> <v3_x>) )
	)
)))

; ------------ Check-Sat ----------------------------
(check-sat)
