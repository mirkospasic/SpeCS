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
(declare-const	<p1_City>	RDFValue)
(declare-const	<p1_Student>	RDFValue)
(declare-const	<p1_University>	RDFValue)
(declare-const	<p1_locatedAt>	RDFValue)
(declare-const	<p1_placeOfBirth>	RDFValue)
(declare-const	<p1_registeredAt>	RDFValue)

; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const	<v2_x>	RDFValue)
(declare-const	<v2_y>	RDFValue)
(declare-const	<v2_z>	RDFValue)

; ------------ Assumption ---------------------------
(assert 
	(and 
		(or (P <v2_x> <a> <p1_Student> <default_graph>) )
		(or (P <v2_x> <p1_registeredAt> <v2_y> <default_graph>) )
		(or (P <v2_y> <a> <p1_University> <default_graph>) )
		(or (P <v2_x> <p1_placeOfBirth> <v2_z> <default_graph>) )
		(or (P <v2_z> <a> <p1_City> <default_graph>) )
		(or (P <v2_y> <p1_locatedAt> <v2_z> <default_graph>) )
	)
)

; ------------ Conjecture ---------------------------
(assert (not (exists ((<v1_x> RDFValue)(<v1_y> RDFValue)(<v1_z> RDFValue)) 
	(and 
		(or (P <v1_x> <a> <p1_Student> <default_graph>) )
		(or (P <v1_x> <p1_registeredAt> <v1_y> <default_graph>) )
		(or (P <v1_x> <p1_placeOfBirth> <v1_z> <default_graph>) )
		(or (P <v1_y> <a> <p1_University> <default_graph>) )
		(or (P <v1_y> <p1_locatedAt> <v1_z> <default_graph>) )
		(or (P <v1_z> <a> <p1_City> <default_graph>) )
		(and (= <v1_x> <v2_x>) (= <v1_y> <v2_y>) (= <v1_z> <v2_z>) )
	)
)))

; ------------ Check-Sat ----------------------------
(check-sat)
