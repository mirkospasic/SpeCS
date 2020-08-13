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
(declare-const	<p1_Student>	RDFValue)
(declare-const	<p1_email>	RDFValue)
(declare-const	<p1_name>	RDFValue)
(declare-const	<p1_shortName>	RDFValue)
(declare-const	<p1_takesCourse>	RDFValue)

; ------------ Literals -----------------------------
(declare-const	<l_0>	RDFValue)
(declare-const	<l_1>	RDFValue)
(declare-const	<l_2>	RDFValue)

; ------------ Variables ----------------------------
(declare-const	<v2_c>	RDFValue)
(declare-const	<v2_email>	RDFValue)
(declare-const	<v2_name>	RDFValue)
(declare-const	<v2_x>	RDFValue)

; ------------ Assumption ---------------------------
(assert 
	(and 
		(or (P <v2_x> <a> <p1_Student> <default_graph>) )
		(or (P <v2_x> <p1_name> <v2_name> <default_graph>) )
		(or (P <v2_x> <p1_email> <v2_email> <default_graph>) )
		(or 
			(and 
				(or (P <v2_x> <p1_takesCourse> <v2_c> <default_graph>) )
				(or (P <v2_c> <p1_shortName> <l_0> <default_graph>) )
			)
			(and 
				(or (P <v2_x> <p1_takesCourse> <v2_c> <default_graph>) )
				(or (P <v2_c> <p1_shortName> <l_1> <default_graph>) )
			)
			(and 
				(or (P <v2_x> <p1_takesCourse> <v2_c> <default_graph>) )
				(or (P <v2_c> <p1_shortName> <l_2> <default_graph>) )
			)
		)
	)
)

; ------------ Conjecture ---------------------------
(assert (not (exists ((<v1_c1> RDFValue)(<v1_c2> RDFValue)(<v1_c> RDFValue)(<v1_email> RDFValue)(<v1_name> RDFValue)(<v1_x> RDFValue)) 
	(and 
		(or (P <v1_x> <a> <p1_Student> <default_graph>) )
		(or (P <v1_x> <p1_name> <v1_name> <default_graph>) )
		(or (P <v1_x> <p1_email> <v1_email> <default_graph>) )
		(or (P <v1_x> <p1_takesCourse> <v1_c1> <default_graph>) )
		(or (P <v1_c1> <p1_shortName> <l_0> <default_graph>) )
		(or (P <v1_x> <p1_takesCourse> <v1_c2> <default_graph>) )
		(or (P <v1_c2> <p1_shortName> <l_1> <default_graph>) )
		(or (P <v1_x> <p1_takesCourse> <v1_c> <default_graph>) )
		(or (P <v1_c> <p1_shortName> <l_2> <default_graph>) )
		(and (= <v1_email> <v2_email>) (= <v1_name> <v2_name>) )
	)
)))

; ------------ Check-Sat ----------------------------
(check-sat)
