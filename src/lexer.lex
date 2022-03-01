%option noyywrap
%option nounput
%{

  /* Lexical analyzer */
  
#include <iostream>
#include <cstdlib>
#include "query.hpp"
using namespace std;

#include "parser.tab.hpp"
 
 
%}

%%
"select"        return select_token;
"where"         return where_token;
"distinct"      return distinct_token;
"limit"         return limit_token;
"offset"        return offset_token;
"from"          return from_token;
"named"         return named_token;
"as"            return as_token;
"union"         return union_token;
"optional"      return optional_token;
"minus"         return minus_token;
"prefix"        return prefix_token;
"order"[ ]+"by" return order_by_token;
"asc"           return asc_token;
"desc"          return desc_token;
"filter"        return filter_token;
"regex"         return regex_token;
"group"[ ]+"by" return group_by_token;
"graph"         return graph_token;
"str"           return builtin_str_token;
"bind"          return bind_token;
"round"         return round_token;
"abs"           return abs_token;
"datatype"      {
  if (string(yytext) == "Datatype") {
    yylval.s = new string(yytext);
    return str_token;
  } 
  return datatype_token;
}
"values"        return values_token;
"contains"      return contains_token;
"lcase"         return lcase_token;
"isliteral"     return is_literal_token;
"isuri"         return is_uri_token;
"bound"         return bound_token;
"a"             return 'a';
"schema:"       return schema_token;
"superquery:"   return superquery_token;
"subquery:"     return subquery_token;
"||"            return or_token;
"&&"            return and_token;
"!="            return noteq_token;
">="            return geq_token;
"<="            return leq_token;
[<][^<>\"{}|^]*[>]  {
  yylval.s = new string(yytext);
  return iri_token;
}
"_:"[a-zA-Z0-9_]+ {
  yylval.s = new string(yytext);
  return blank_node_token;
}
["][^\"]*["]    {
  yylval.s = new string(yytext);
  return string_token;
}
[?][a-zA-Z_0-9]*   {
  yylval.s = new string(yytext);
  return var_token;
}
[0-9]+           {
  yylval.i = atoi(yytext);
  return int_token;
}
[.;,:a{}()+*/<>=!-]         return *yytext;
[a-zA-Z_0-9-]+   {
  yylval.s = new string(yytext);
  return str_token;
}
[ \t\n]     {   }
.           {
  cerr << "Lexical error: unknown character '" << *yytext << "'" << endl;
  exit(EXIT_FAILURE);
}

%%


