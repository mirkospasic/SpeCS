#include <iostream>
#include <string>
#include <cstdlib>
#include <fstream>
#include <chrono>
#include <cstring>
#include "query.hpp"
#include "parser.tab.hpp"

using namespace std;

char *filename = (char *)"formula";

/* Error function */
void yyerror(string s) {
  cerr << s << " in " << filename << endl;
  exit(EXIT_FAILURE);
}

Query *subQuery = nullptr;
Query *superQuery = nullptr;
Query *schema = nullptr;

/* Main function */
int main(int argc, char **argv) {
  // For debugging purposes
  //yydebug = 1;

  // For measuring times
  auto start = chrono::high_resolution_clock::now();

  //Analysis of cmd arguments
  bool valid_arguments = false;
  bool rename = false;
  extern FILE* yyin;
  if ((argc >= 3) && (string("-file") == argv[1])) {
    filename = argv[2];
    if ((yyin = fopen(filename, "r")) == NULL)
      yyerror(string("File ") + filename + " cannot be open for reading");
    valid_arguments = true;
    if (argc > 3 && (string("-rename") == argv[3]))
      rename = true;
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
  
  if (valid_arguments == false) {
    cout <<"usage: " << endl;
    cout << "\t" << argv[0] << " -file file_with_2_sparql_queries [-rename]" << endl;
    cout << "\t" << argv[0] << " -superquery q1 -subquery q2 [-schema sc] [-rename]" << endl;
    return 0;
  }
  

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
  auto dur1 = end1 - start;


  // Formula generation 
  if (superQuery->getLimit() >= 0 && ((subQuery->getLimit() >= 0 && superQuery->getLimit() < subQuery->getLimit()) || subQuery->getLimit() < 0)) {
    //cout << "sat - Super query cannot have limit less than subquery" << endl;
    //return 0;
  }

  subQuery->addCommonPrefixes();
  superQuery->addCommonPrefixes();
  
  set<string> subQueryProjVars = subQuery->projVars();
  set<string> superQueryProjVars = superQuery->projVars();

  if (subQueryProjVars.size() > superQueryProjVars.size()) {
    cout << "sat - Number of projections (or variables) in subquery cannot be greater than the number in superquery" << endl;
    return 0;
  }

  // Is it allowed to use differently named projection variables
  if (rename == false) {
    for (auto p : subQueryProjVars) {
      bool found = false;
      string pp = p.substr(4, p.size()-5);
      for (auto q : superQueryProjVars) {
	string qq = q.substr(4, q.size()-5);
	if (pp == qq) {
	  found = true;
	  break;
	}
      }
      if (!found) {
	cout << "sat - Projection " << pp << " from subquery is not present in superquery" << endl;
	return 0;
      }
    }
  }

  
  set<string> superQueryFroms = superQuery->getFrom();
  set<string> subQueryFroms = subQuery->getFrom();
  superQueryFroms.erase("<default_graph>");
  subQueryFroms.erase("<default_graph>");
  set<string> superQueryFromNamed = superQuery->getFromNamed();
  set<string> subQueryFromNamed = subQuery->getFromNamed();
  ///*
  if (superQueryFroms.size() != 0) {
    for (auto a : subQueryFroms)
      if (!superQueryFroms.count(a)) {
	//cout << filename << endl;
	cout << "sat - Froms in subquery is not subset of froms in superquery" << endl;
	return 0;
      }
    if (subQueryFroms.size() == 0) {
      //cout << filename << endl;
      cout << "sat - Froms in subquery is not subset of froms in superquery" << endl;
      return 0;
    }
  }
  //*/
  
  ofstream output;
  string outputname = string(filename) + ".smt";
  output.open(outputname);

  output << "; ------------ Sort and Predicate -------------------" << endl;
  output << common_formula() << endl;

  output << "; ------------ IRIs ---------------------------------" << endl;
  set<string> subQueryIRIs = subQuery->allIRIs();
  set<string> superQueryIRIs = superQuery->allIRIs();
  set<string> schemaIRIs;
  set<string> iris = subQueryIRIs;
  iris.insert(superQueryIRIs.begin(), superQueryIRIs.end());
  if (schema != nullptr) {
    schemaIRIs = schema->allIRIs();
    schemaIRIs.insert("<a>");
    iris.insert(schemaIRIs.begin(), schemaIRIs.end());
  }
  for (auto a : subQuery->getFrom())
    iris.insert(a);
  for (auto a : subQuery->getFromNamed())
    iris.insert(a);
  for (auto a : superQuery->getFrom())
    iris.insert(a);
  for (auto a : superQuery->getFromNamed())
    iris.insert(a);
  for (auto a : iris) {
    if (a != "<default_graph>")
      output << "(declare-const\t" << a << "\tRDFValue)" << endl;
  }
  output << endl;


  output << "; ------------ Literals -----------------------------" << endl;
  set<string> subQueryLiterals = subQuery->allLiterals();
  set<string> superQueryLiterals = superQuery->allLiterals();
  for (auto a : subQueryLiterals)
    output << "(declare-const\t" << a << "\tRDFValue)" << endl;
  for (auto a : superQueryLiterals)
    if (!subQueryLiterals.count(a))
      output << "(declare-const\t" << a << "\tRDFValue)" << endl;
  output << endl;

  if (schema != nullptr) {
    output << "; ------------ Schema -------------------------------" << endl;
    output << "(assert " << endl;
    output << schema->schemaFormula(1) << endl;
    output << ")" << endl << endl;
  }
  
  set<string> subQueryVariables = subQuery->allVariables();
  set<string> superQueryVariables = superQuery->allVariables();
  output << "; ------------ Variables ----------------------------" << endl;
  for (auto a : subQueryVariables)
    output << "(declare-const\t" << a << "\tRDFValue)" << endl;
  output << endl;
  
  output << "; ------------ Assumption ---------------------------" << endl;
  output << "(assert " << endl;
  output << subQuery->formula(1) << endl;
  output << ")" << endl << endl;

  output << "; ------------ Conjecture ---------------------------" << endl;
  output << "(assert (not (exists (";
  for (auto a : superQueryVariables)
    output << "(" << a << " RDFValue)";
  output << ") " << endl;
  string conjecture = superQuery->formula(1);
  try {
    conjecture = conjecture.substr(0, conjecture.size()-1) + "\t" + eqProj(superQueryProjVars, subQueryProjVars, rename) + "\n\t)";
  }
  catch (string s) {
    cout << "sat - " << s << endl;
    return 0;
  }
  output << conjecture << endl;
  output << ")))" << endl << endl;
  
  output << "; ------------ Check-Sat ----------------------------" << endl;
  output << "(check-sat)" << endl;
  
  fclose(yyin);
  output.close();

  delete subQuery;
  delete superQuery;

  // Measuring times needed for formula generation
  auto end2 = chrono::high_resolution_clock::now();
  auto dur2 = end2 - end1;

  // Execute z3 solver with 60s timeout 
  string solve = "z3 -T:60 -smt2 " + outputname;
  system(solve.c_str());

  // Measuring times needed for z3
  auto end3 = chrono::high_resolution_clock::now();
  auto dur3 = end3 - end2;

  // Writing of execution times
  //cerr << chrono::duration_cast<std::chrono::nanoseconds>(dur1).count() << ";";
  //cerr << chrono::duration_cast<std::chrono::nanoseconds>(dur2).count() << ";";
  //cerr << chrono::duration_cast<std::chrono::nanoseconds>(dur3).count() << endl;

  return 0;
}
