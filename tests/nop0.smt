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
(declare-const	<iri0>	RDFValue)
(declare-const	<iri1>	RDFValue)
(declare-const	<p1_nesto1>	RDFValue)
(declare-const	<p1_nesto2>	RDFValue)
(declare-const	<p1_takesCourse>	RDFValue)

; ------------ Literals -----------------------------
(declare-const	<l_0>	RDFValue)

; ------------ Variables ----------------------------
(declare-const	<v1_a>	RDFValue)
(declare-const	<v1_b>	RDFValue)
(declare-const	<v1_x>	RDFValue)

; ------------ Assumption ---------------------------
(assert 
	(and 
		(or (P <v1_x> <p1_takesCourse> <l_0> <iri0>) (P <v1_x> <p1_takesCourse> <l_0> <iri1>) )
		(or (P <v1_x> <p1_nesto1> <v1_a> <iri0>) (P <v1_x> <p1_nesto1> <v1_a> <iri1>) )
		(or (P <v1_x> <p1_nesto2> <v1_b> <iri0>) (P <v1_x> <p1_nesto2> <v1_b> <iri1>) )
	)
)

; ------------ Conjecture ---------------------------
(assert (not (exists ((<v2_a> RDFValue)(<v2_b> RDFValue)(<v2_x> RDFValue)) 
	(and 
		(or (P <v2_x> <p1_takesCourse> <l_0> <iri0>) (P <v2_x> <p1_takesCourse> <l_0> <iri1>) )
		(or 
			(and 
				(or (P <v2_x> <p1_nesto1> <v2_a> <iri0>) (P <v2_x> <p1_nesto1> <v2_a> <iri1>) )
				(or (P <v2_x> <p1_nesto2> <v2_b> <iri0>) (P <v2_x> <p1_nesto2> <v2_b> <iri1>) )
			)
			(forall ((<v2_a> RDFValue)(<v2_b> RDFValue))
				(not 
					(and 
						(or (P <v2_x> <p1_nesto1> <v2_a> <iri0>) (P <v2_x> <p1_nesto1> <v2_a> <iri1>) )
						(or (P <v2_x> <p1_nesto2> <v2_b> <iri0>) (P <v2_x> <p1_nesto2> <v2_b> <iri1>) )
					)
				)
			)
		)
		(and (= <v2_x> <v1_x>) )
	)
)))

; ------------ Check-Sat ----------------------------
(check-sat)
