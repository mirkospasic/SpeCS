#include <iostream>
#include <string>
#include <cstdlib>
#include <fstream>
#include <chrono>
#include <cstring>
#include "query.hpp"
#include "parser.tab.hpp"
#include <memory>
#include <stdexcept>
#include <array>

extern int yydebug;

using namespace std;

char *filename = (char *)"formula";

/* Error function */
void yyerror(string s) {
  cerr << s << " in " << filename << endl;
  exit(EXIT_FAILURE);
}

/* Function for executing cmd command */
std::string exec(const char* cmd) {
    std::array<char, 128> buffer;
    std::string result;
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd, "r"), pclose);
    if (!pipe) {
        throw std::runtime_error("popen() failed!");
    }
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }
    return result;
}

Query *subQuery = nullptr;
Query *superQuery = nullptr;
Query *schema = nullptr;

/* Main function */
int main(int argc, char **argv) {
  // For debugging purposes
  //yydebug = 1;

  // For measuring times
  auto start1 = chrono::high_resolution_clock::now();

  //Analysis of cmd arguments
  bool valid_arguments = false;
  bool rename = false;
  bool qc_strict = false;
  bool eq_check = false;
  bool axiomatic_triples = false;
  
  extern FILE* yyin;
  if ((argc >= 3) && (string("-file") == argv[1])) {
    filename = argv[2];
    if ((yyin = fopen(filename, "r")) == NULL)
      yyerror(string("File ") + filename + " cannot be open for reading");
    valid_arguments = true;
    if (argc > 3 && (string("-rename") == argv[3]))
      rename = true;
    else if (argc > 4 && (string("-rename") == argv[4]))
      rename = true;
    else if (argc > 5 && (string("-rename") == argv[5]))
      rename = true;
    else if (argc > 6 && (string("-rename") == argv[6]))
      rename = true;
    if (argc > 3 && (string("-qc") == argv[3]))
      qc_strict = true;
    else if (argc > 4 && (string("-qc") == argv[4]))
      qc_strict = true;
    else if (argc > 5 && (string("-qc") == argv[5]))
      qc_strict = true;
    else if (argc > 6 && (string("-qc") == argv[6]))
      qc_strict = true;
    if (argc > 3 && (string("-eq") == argv[3]))
      eq_check = true;
    else if (argc > 4 && (string("-eq") == argv[4]))
      eq_check = true;
    else if (argc > 5 && (string("-eq") == argv[5]))
      eq_check = true;
    else if (argc > 6 && (string("-eq") == argv[6]))
      eq_check = true;
    if (argc > 3 && (string("-axiomatic") == argv[3]))
      axiomatic_triples = true;
    else if (argc > 4 && (string("-axiomatic") == argv[4]))
      axiomatic_triples = true;
    else if (argc > 5 && (string("-axiomatic") == argv[5]))
      axiomatic_triples = true;
    else if (argc > 6 && (string("-axiomatic") == argv[6]))
      axiomatic_triples = true;
  }
  else {
    int arg_no = 1;
    char *superquery_txt = nullptr;
    char *subquery_txt = nullptr;
    char *schema_txt = nullptr;
    while (arg_no < argc) {
      if (argv[arg_no] == string("-superquery")) {
	arg_no++;
	if (arg_no == argc)
	  yyerror("Missing superquery");
	superquery_txt = argv[arg_no];
	arg_no++;
      }
      else if (argv[arg_no] == string("-subquery")) {
	arg_no++;
	if (arg_no == argc)
	  yyerror("Missing subquery");
	subquery_txt = argv[arg_no];
	arg_no++;
      }
      else if (argv[arg_no] == string("-schema")) {
	arg_no++;
	if (arg_no == argc)
	  yyerror("Missing schema");
	schema_txt = argv[arg_no];
	arg_no++;
      }
      else if (argv[arg_no] == string("-rename")) {
	arg_no++;
	rename = true;
      }
      else if (argv[arg_no] == string("-qc")) {
	arg_no++;
	qc_strict = true;
      }
      else if (argv[arg_no] == string("-eq")) {
	arg_no++;
	eq_check = true;
      }
      else if (argv[arg_no] == string("-axiomatic")) {
	arg_no++;
	axiomatic_triples = true;
      }
      else {
	cerr << "Unknown argument" << argv[arg_no] << endl;
	break;
      }
    }
    if ((superquery_txt != nullptr) && (subquery_txt != nullptr)) {
      unsigned length = strlen(superquery_txt) + strlen(subquery_txt) + 32;
      if (schema_txt != nullptr)
	length += strlen(schema_txt) + 16;
      
      char* buffer = (char*)malloc(length * sizeof(char));
      if (buffer == nullptr)
	yyerror("malloc() error");

      buffer[0] = '\0';
      if (schema_txt != nullptr) {
	strcpy(buffer + strlen(buffer), "schema:\n");
	strcpy(buffer + strlen(buffer), schema_txt);
	strcpy(buffer + strlen(buffer), "\n\n");
      }
      strcpy(buffer + strlen(buffer), "superquery:\n");
      strcpy(buffer + strlen(buffer), superquery_txt);
      strcpy(buffer + strlen(buffer), "\n\n");
      strcpy(buffer + strlen(buffer), "subquery:\n");
      strcpy(buffer + strlen(buffer), subquery_txt);
      //cout << buffer << endl;
      yyin = fmemopen(buffer, strlen(buffer), "r");
      valid_arguments = true;
    }
  }
  
  if (valid_arguments == false)
    yyerror(string("usage: \n") +
	    "\t" + argv[0] + " -file file_with_2_sparql_queries [-qc] [-rename] [-eq]\n" +
	    "\t" + argv[0] + " -superquery q1 -subquery q2 [-schema sc] [-qc] [-rename] [-eq]\n"
	    );

  // Parsing
  try {
    yyparse();
  }
  catch (const char *s) {
    cout << s << endl;
    return 1;
  }

  // Measuring parsing times
  auto end1 = chrono::high_resolution_clock::now();
  auto dur1 = end1 - start1;
  long long dur2 = 0;
  
  subQuery->addCommonPrefixes();
  superQuery->addCommonPrefixes();

  superQuery->allIRIs();
  superQuery->allLiterals();
  superQuery->allVariables();
  
  
  // Formula generation starts

  // Normalizing queries
  subQuery->normalize();
  superQuery->normalize();
  if (schema != nullptr)
    schema->normalize();
    
  set<string> superQueryFroms = superQuery->getFrom();
  set<string> subQueryFroms = subQuery->getFrom();
  superQueryFroms.erase("<default_graph>");
  subQueryFroms.erase("<default_graph>");
  set<string> superQueryFromNamed = superQuery->getFromNamed();
  set<string> subQueryFromNamed = subQuery->getFromNamed();

  if (eq_check) {
    //if (superQuery->getLimit() >= 0 && ((subQuery->getLimit() >= 0 && superQuery->getLimit() < subQuery->getLimit()) || subQuery->getLimit() < 0)) {
    if (subQuery->getLimit() != superQuery->getLimit()) {
      cout << "sat - limit" << endl;
      goto end;
    }

    if (subQuery->getOffset() != superQuery->getOffset()) {
      cout << "sat - offset" << endl;
      goto end;
    }

    vector<pair<RDFValue *, bool>> v1, v2;
    v1 = superQuery->getOrderBy();
    v2 = subQuery->getOrderBy();
    bool order_tmp = true;
    if (v1.size() != v2.size())
      order_tmp = false;
    for (unsigned i = 0; i < v1.size(); i++) {
      if (v1[i].second != v2[i].second)
	order_tmp = false;
      //TODO: Check variables as well
    }
    if (order_tmp == false) {
      cout << "sat - order" << endl;
      goto end;
    }    
  }


  ///*
  if (superQueryFroms.size() != 0) {
    for (auto a : subQueryFroms)
      if (!superQueryFroms.count(a)) {
	//cout << filename << endl;
	cout << "sat - Froms in subquery is not subset of froms in superquery" << endl;
	goto end;
      }
    if (subQueryFroms.size() == 0) {
      //cout << filename << endl;
      cout << "sat - Froms in subquery is not subset of froms in superquery" << endl;
      goto end;
    }
  }
  //*/

  //cout << subQuery->formula(1) << endl;
  //cout << superQuery->formula(1) << endl;
  //return 0;
  
  for (unsigned union_i = 0; union_i < subQuery->numberOfConjuctive(); union_i++) {
    bool ok = false;
    for (unsigned union_j = 0; union_j < superQuery->numberOfConjuctive(); union_j++) {
      bool check_unsatisfiability_of_q1 = false;
      //cout << union_i << " " << union_j << endl;
      
      Query* subQuery1 = subQuery->i_th_query(union_i);
      Query* superQuery1 = superQuery->i_th_query(union_j);
      
      set<string> subQuery1Variables = subQuery1->allVariables();
      set<string> superQuery1Variables = superQuery1->allVariables();
      
      set<string> subQuery1ProjVars = subQuery1->projVars();
      set<string> superQuery1ProjVars = superQuery1->projVars();
      
      set<string> subQuery1ProjVarsIntersect, superQuery1ProjVarsIntersect;
      for (auto a : subQuery1Variables)
	if (subQuery1ProjVars.count(a))
	  subQuery1ProjVarsIntersect.insert(a.replace(1, 3, ""));
      for (auto a : superQuery1Variables)
	if (superQuery1ProjVars.count(a))
	  superQuery1ProjVarsIntersect.insert(a.replace(1, 3, ""));

      /*
      for (auto a : superQuery1Variables)
	cout << a << endl;
      cout << "---------------" << endl;
      for (auto a : superQuery1ProjVars)
	cout << a << endl;
      cout << "---------------" << endl;
      for (auto a : superQuery1ProjVarsIntersect)
	cout << a << endl;
      cout << "---------------" << endl;
      */

      if (qc_strict) {
	if (rename) {
	  if (subQuery1ProjVarsIntersect.size() != superQuery1ProjVarsIntersect.size()) {
	    //cout << "sat - constraint over sets" << union_i << " " << union_j << endl;
	    //continue;
	    check_unsatisfiability_of_q1 = true;
	  }
	}
	else {
	  if (subQuery1ProjVarsIntersect != superQuery1ProjVarsIntersect) {
	    //cout << "sat - constraint over sets" << union_i << " " << union_j << endl;
	    //continue;
	    check_unsatisfiability_of_q1 = true;
	  }
	}
      }
      else {
	if (rename) {
	  if (subQuery1ProjVarsIntersect.size() > superQuery1ProjVarsIntersect.size()) {
	    //cout << "sat - constraint over sets" << union_i << " " << union_j << endl;
	    //continue;
	    check_unsatisfiability_of_q1 = true;
	  }
	}
	else {
	  bool ret = false;
	  for (auto a : subQuery1ProjVarsIntersect)
	    if (superQuery1ProjVarsIntersect.count(a) == 0) {
	      ret = true;
	      break;
	    }
	  if (ret) {
	    //cout << "sat - constraint over sets" << union_i << " " << union_j << endl;
	    //continue;
	    check_unsatisfiability_of_q1 = true;
	  }
	}
      }
      
      
      ofstream output;
      string outputname = string(filename) + ".smt";
      output.open(outputname);
      
      output << "; ------------ Sort and Predicate -------------------" << endl;
      output << common_formula() << endl;
      
      output << "; ------------ IRIs ---------------------------------" << endl;
      set<string> subQuery1IRIs = subQuery1->allIRIs();
      set<string> superQuery1IRIs = superQuery1->allIRIs();
      set<string> schemaIRIs;
      set<string> iris = subQuery1IRIs;
      iris.insert(superQuery1IRIs.begin(), superQuery1IRIs.end());
      if (schema != nullptr) {
	schemaIRIs = schema->allIRIs();
	schemaIRIs.insert("<a>");
	if (axiomatic_triples) {
	  schemaIRIs.insert("<p0_Class>");
	  schemaIRIs.insert("<p0_Container>");
	  schemaIRIs.insert("<p0_ContainerMembershipProperty>");
	  schemaIRIs.insert("<p0_Datatype>");
	  schemaIRIs.insert("<p0_Literal>");
	  schemaIRIs.insert("<p0_Resource>");
	  schemaIRIs.insert("<p0_Resourse>");
	  schemaIRIs.insert("<p0_comment>");
	  schemaIRIs.insert("<p0_domain>");
	  schemaIRIs.insert("<p0_isDefinedBy>");
	  schemaIRIs.insert("<p0_label>");
	  schemaIRIs.insert("<p0_member>");
	  schemaIRIs.insert("<p0_range>");
	  schemaIRIs.insert("<p0_seeAlso>");
	  schemaIRIs.insert("<p0_subClassOf>");
	  schemaIRIs.insert("<p0_subPropertyOf>");
	  schemaIRIs.insert("<p1_headOf>");
	  schemaIRIs.insert("<p1_maleHeadOf>");
	  schemaIRIs.insert("<p_Alt>");
	  schemaIRIs.insert("<p_Bag>");
	  schemaIRIs.insert("<p_List>");
	  schemaIRIs.insert("<p_Property>");
	  schemaIRIs.insert("<p_Seq>");
	  schemaIRIs.insert("<p_Statement>");
	  schemaIRIs.insert("<p_XMLLiteral>");
	  schemaIRIs.insert("<p__1>");
	  schemaIRIs.insert("<p__2>");
	  schemaIRIs.insert("<p_first>");
	  schemaIRIs.insert("<p_object>");
	  schemaIRIs.insert("<p_predicate>");
	  schemaIRIs.insert("<p_rest>");
	  schemaIRIs.insert("<p_subject>");
	  schemaIRIs.insert("<p_type>");
	  schemaIRIs.insert("<p_value>");
	}
	iris.insert(schemaIRIs.begin(), schemaIRIs.end());
      }
      for (auto a : subQuery1->getFrom())
	iris.insert(a);
      for (auto a : subQuery1->getFromNamed())
	iris.insert(a);
      for (auto a : superQuery1->getFrom())
	iris.insert(a);
      for (auto a : superQuery1->getFromNamed())
	iris.insert(a);
      for (auto a : iris) {
	if (a != "<default_graph>")
	  output << "(declare-const\t" << a << "\tRDFValue)" << endl;
	size_t index = a.find("_Class");
	if (index != string::npos) {
	  iris.insert("<p0_subClassOf>");
	}
	index = a.find("_Property");
	if (index != string::npos) {
	  iris.insert("<p0_subPropertyOf>");
	}
	index = a.find("_ContainerMembershipProperty");
	if (index != string::npos) {
	  iris.insert("<p0_subPropertyOf>");
	  iris.insert("<p0_member>");
	}
	index = a.find("_Datatype");
	if (index != string::npos) {
	  iris.insert("<p0_subClassOf>");
	}
	iris.insert("<p_Property>");
	iris.insert("<p0_Resourse>");
      }
      output << endl;
      
      
      output << "; ------------ Literals -----------------------------" << endl;
      set<string> subQuery1Literals = subQuery1->allLiterals();
      set<string> superQuery1Literals = superQuery1->allLiterals();
      for (auto a : subQuery1Literals)
	output << "(declare-const\t" << a << "\tRDFValue)" << endl;
      for (auto a : superQuery1Literals)
	if (!subQuery1Literals.count(a))
	  output << "(declare-const\t" << a << "\tRDFValue)" << endl;
      output << endl;
      
      if (schema != nullptr) {
	output << "; ------------ Schema -------------------------------" << endl;
	output << "(assert " << endl;
	output << schema->schemaFormula(1, false) << endl;
	output << ")" << endl << endl;
	output << "(assert " << endl;
	output << schema->schemaFormula(1) << endl;
	output << ")" << endl << endl;
	output << "(assert " << endl;
	output << "\t(and " << endl;
	output << tabs(2) + "(forall ((s RDFValue)(p RDFValue)(o RDFValue)(g RDFValue)) (=> (P s p o g) (P p <a> <p_Property> g)))" << endl;
	output << tabs(2) + "(forall ((s RDFValue)(p RDFValue)(o RDFValue)(g RDFValue)) (=> (P s p o g) (P s <a> <p0_Resourse> g)))" << endl;
	output << tabs(2) + "(forall ((s RDFValue)(p RDFValue)(o RDFValue)(g RDFValue)) (=> (P s p o g) (P o <a> <p0_Resourse> g)))" << endl;
	output << "\t)" << endl;
	output << ")" << endl << endl;
	if (axiomatic_triples) {
	  output << "(assert " << endl;
	  output << "\t(and " << endl;
	  output << tabs(2) + "(P <p1_maleHeadOf> <p0_subPropertyOf> <p1_headOf> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_type> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_domain> <p0_domain> <p_Property> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_range> <p0_domain> <p_Property> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_subPropertyOf> <p0_domain> <p_Property> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_subClassOf> <p0_domain> <p0_Class> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_subject> <p0_domain> <p_Statement> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_predicate> <p0_domain> <p_Statement> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_object> <p0_domain> <p_Statement> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_member> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_first> <p0_domain> <p_List> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_rest> <p0_domain> <p_List> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_seeAlso> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_isDefinedBy> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_comment> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_label> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_value> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_type> <p0_range> <p0_Class> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_domain> <p0_range> <p0_Class> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_range> <p0_range> <p0_Class> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_subPropertyOf> <p0_range> <p_Property> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_subClassOf> <p0_range> <p0_Class> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_subject> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_predicate> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_object> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_member> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_first> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_rest> <p0_range> <p_List> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_seeAlso> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_isDefinedBy> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_comment> <p0_range> <p0_Literal> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_label> <p0_range> <p0_Literal> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_value> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_Alt> <p0_subClassOf> <p0_Container> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_Bag> <p0_subClassOf> <p0_Container> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_Seq> <p0_subClassOf> <p0_Container> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_ContainerMembershipProperty> <p0_subClassOf> <p_Property> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_isDefinedBy> <p0_subPropertyOf> <p0_seeAlso> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_XMLLiteral> <p_type> <p0_Datatype> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p_XMLLiteral> <p0_subClassOf> <p0_Literal> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p0_Datatype> <p0_subClassOf> <p0_Class> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p__1> <p_type> <p0_ContainerMembershipProperty> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p__1> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p__1> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p__2> <p_type> <p0_ContainerMembershipProperty> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p__2> <p0_domain> <p0_Resource> <default_graph>)" << endl; 
	  output << tabs(2) + "(P <p__2> <p0_range> <p0_Resource> <default_graph>)" << endl; 
	  output << "\t)" << endl;
	  output << ")" << endl << endl;
	}
      }
      
      output << "; ------------ Variables ----------------------------" << endl;
      for (auto a : subQuery1Variables)
	output << "(declare-const\t" << a << "\tRDFValue)" << endl;
      output << endl;
      
      output << "; ------------ Assumption ---------------------------" << endl;
      output << "(assert " << endl;
      output << subQuery1->formula(1) << endl;
      output << ")" << endl << endl;
      //cout << "---------------" << endl;
      //cout << subQuery1->formula(1) << endl;
      //cout << "---------------" << endl;
      //cout << superQuery1->formula(1) << endl;
      //cout << "---------------" << endl;

      if (check_unsatisfiability_of_q1 == false) {
	output << "; ------------ Conjecture ---------------------------" << endl;
	output << "(assert (not (exists (";
	for (auto a : superQuery1ProjVars)
	  output << "(" << a << " RDFValue)";
	for (auto a : superQuery1Variables)
	  if (superQuery1ProjVars.count(a) == 0)
	    output << "(" << a << " RDFValue)";
	output << ") " << endl;
	string conjecture = superQuery1->formula(1);
	try {
	  conjecture = conjecture.substr(0, conjecture.size()-1) + "\t" + eqProj(superQuery1ProjVars, subQuery1ProjVars, rename) + "\n\t)";
	}
	catch (string s) {
	  //cout << "sat - " << s << endl;
	  continue;
	}
	output << conjecture << endl;
	output << ")))" << endl << endl;
      }
      
      output << "; ------------ Check-Sat ----------------------------" << endl;
      output << "(check-sat)" << endl;
      
      output.close();
      
      //delete subQuery1;
      //delete superQuery1;
      
      // Measuring times needed for z3
      auto start2 = chrono::high_resolution_clock::now();
      
      // Execute z3 solver with 60s timeout 
      string solve = "z3 -T:60 -smt2 " + outputname;
      string result = exec(solve.c_str());
      if (result.substr(0, 5) == "unsat")
	ok = true;
      
      // Measuring times needed for z3
      auto end2 = chrono::high_resolution_clock::now();
      dur2 += chrono::duration_cast<std::chrono::nanoseconds>(end2 - start2).count();

      if (ok) {
	//cout << "ok" << union_i << " " << union_j << endl;
	break;
      }
    }
    if (!ok) {
      cout << "sat - " << union_i << endl;
      goto end;
    }
  }

  fclose(yyin);
  cout << "unsat" << endl;

 end:
  // Measuring total time
  auto end3 = chrono::high_resolution_clock::now();
  auto dur3 = end3 - start1;
  
  // Writing of execution times
  //cerr << chrono::duration_cast<std::chrono::nanoseconds>(dur1).count() << ";";
  //cerr << dur2 << ";";
  //cerr << chrono::duration_cast<std::chrono::nanoseconds>(dur3).count() << endl;
  
  return 0;
}
