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
(declare-const	<p2_subClassOf>	RDFValue)

; ------------ Literals -----------------------------

; ------------ Schema -------------------------------
(assert 
	(and 
		(forall ((x RDFValue)(g RDFValue)) (=> (P x <a> <p1_GraduateStudent> g) (P x <a> <p1_Student> g)))
		(forall ((x RDFValue)(g RDFValue)) (=> (P x <a> <p1_UndergradStudent> g) (P x <a> <p1_Student> g)))
	)
)

; ------------ Variables ----------------------------
(declare-const	<v3_x>	RDFValue)

; ------------ Assumption ---------------------------
(assert 
	(and 
		(or 
			(and 
				(or (P <v3_x> <a> <p1_GraduateStudent> <default_graph>) )
			)
			(and 
				(or (P <v3_x> <a> <p1_UndergradStudent> <default_graph>) )
			)
		)
	)
)

; ------------ Conjecture ---------------------------
(assert (not (exists ((<v2_x> RDFValue)) 
	(and 
		(or (P <v2_x> <a> <p1_GraduateStudent> <default_graph>) )
		(and (= <v2_x> <v3_x>) )
	)
)))

; ------------ Check-Sat ----------------------------
(check-sat)
