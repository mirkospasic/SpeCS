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
(declare-const	<p1_age>	RDFValue)
(declare-const	<p1_emailAddress>	RDFValue)
(declare-const	<p1_memberOf>	RDFValue)
(declare-const	<p1_name>	RDFValue)
(declare-const	<p1_nickName>	RDFValue)
(declare-const	<p1_sex>	RDFValue)
(declare-const	<p1_ssn>	RDFValue)
(declare-const	<p1_takesCourse>	RDFValue)
(declare-const	<p1_telephone>	RDFValue)

; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const	<v2_age>	RDFValue)
(declare-const	<v2_course>	RDFValue)
(declare-const	<v2_dept>	RDFValue)
(declare-const	<v2_email>	RDFValue)
(declare-const	<v2_sex>	RDFValue)
(declare-const	<v2_ssn>	RDFValue)
(declare-const	<v2_tel>	RDFValue)
(declare-const	<v2_x>	RDFValue)
(declare-const	<v2_y>	RDFValue)
(declare-const	<v2_z>	RDFValue)

; ------------ Assumption ---------------------------
(assert 
	(and 
		(or (P <v2_x> <a> <p1_Student> <default_graph>) )
		(or 
			(and 
				(or (P <v2_x> <p1_name> <v2_y> <default_graph>) )
			)
			(and 
				(or (P <v2_x> <p1_nickName> <v2_z> <default_graph>) )
				(or (P <v2_x> <p1_telephone> <v2_tel> <default_graph>) )
				(or (P <v2_x> <p1_ssn> <v2_ssn> <default_graph>) )
				(or (P <v2_x> <p1_sex> <v2_sex> <default_graph>) )
				(or (P <v2_x> <p1_memberOf> <v2_dept> <default_graph>) )
				(or (P <v2_x> <p1_emailAddress> <v2_email> <default_graph>) )
				(or (P <v2_x> <p1_age> <v2_age> <default_graph>) )
			)
		)
		(or (P <v2_x> <p1_takesCourse> <v2_course> <default_graph>) )
	)
)

; ------------ Conjecture ---------------------------
(assert (not (exists ((<v1_age> RDFValue)(<v1_course> RDFValue)(<v1_dept> RDFValue)(<v1_email> RDFValue)(<v1_sex> RDFValue)(<v1_ssn> RDFValue)(<v1_tel> RDFValue)(<v1_x> RDFValue)(<v1_y> RDFValue)(<v1_z> RDFValue)) 
	(and 
		(or (P <v1_x> <a> <p1_Student> <default_graph>) )
		(or 
			(and 
				(or (P <v1_x> <p1_name> <v1_y> <default_graph>) )
			)
			(and 
				(or (P <v1_x> <p1_nickName> <v1_z> <default_graph>) )
			)
			(and 
				(or (P <v1_x> <p1_telephone> <v1_tel> <default_graph>) )
			)
			(and 
				(or (P <v1_x> <p1_ssn> <v1_ssn> <default_graph>) )
			)
			(and 
				(or (P <v1_x> <p1_sex> <v1_sex> <default_graph>) )
			)
			(and 
				(or (P <v1_x> <p1_memberOf> <v1_dept> <default_graph>) )
			)
			(and 
				(or (P <v1_x> <p1_emailAddress> <v1_email> <default_graph>) )
			)
			(and 
				(or (P <v1_x> <p1_age> <v1_age> <default_graph>) )
			)
		)
		(or (P <v1_x> <p1_takesCourse> <v1_course> <default_graph>) )
		(and (= <v1_age> <v2_age>) (= <v1_course> <v2_course>) (= <v1_dept> <v2_dept>) (= <v1_email> <v2_email>) (= <v1_sex> <v2_sex>) (= <v1_ssn> <v2_ssn>) (= <v1_tel> <v2_tel>) (= <v1_x> <v2_x>) (= <v1_y> <v2_y>) (= <v1_z> <v2_z>) )
	)
)))

; ------------ Check-Sat ----------------------------
(check-sat)
