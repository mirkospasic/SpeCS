#include "query.hpp"

#include <iostream>
using namespace std;

string common_formula() {
  string res;
  res += "(declare-sort RDFValue 0)\n";
  res += "(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)\n";

  res += "(declare-fun f_str (RDFValue) RDFValue)\n";
  res += "(declare-fun f_xsd_string (RDFValue) RDFValue)\n";
  res += "(declare-fun f_datatype (RDFValue) RDFValue)\n";
  res += "(declare-fun f_lcase (RDFValue) RDFValue)\n";
  res += "(declare-fun f_round (RDFValue) RDFValue)\n";
  res += "(declare-fun f_abs (RDFValue) RDFValue)\n";
  res += "(declare-fun f_isliteral (RDFValue) Bool)\n";
  res += "(declare-fun f_isuri (RDFValue) Bool)\n";
  res += "(declare-fun f_contains (RDFValue RDFValue) Bool)\n";
  res += "(declare-fun f_regex (RDFValue RDFValue) Bool)\n";
  res += "(declare-fun f_add (RDFValue RDFValue) RDFValue)\n";
  res += "(declare-fun f_sub (RDFValue RDFValue) RDFValue)\n";
  res += "(declare-fun f_mul (RDFValue RDFValue) RDFValue)\n";
  res += "(declare-fun f_div (RDFValue RDFValue) RDFValue)\n";
  res += "(declare-fun f_lt (RDFValue RDFValue) Bool)\n";
  res += "(declare-fun f_gt (RDFValue RDFValue) Bool)\n";
  res += "(declare-fun f_leq (RDFValue RDFValue) Bool)\n";
  res += "(declare-fun f_geq (RDFValue RDFValue) Bool)\n";
  res += "(declare-fun f_bound (RDFValue) Bool)\n";

  res += "(declare-const <default_graph> RDFValue)\n";
  res += "(assert (forall ((s RDFValue)(p RDFValue)(o RDFValue)(g RDFValue)) (=> (P s p o g) (P s p o <default_graph>))))\n";
  
  //res += "(assert (forall ((s RDFValue)(p RDFValue)(o RDFValue)(g RDFValue)) (=> (P s p o g) (and (f_bound s) (f_bound p) (f_bound o) (f_bound g)))))\n";
  //res += "(assert (forall ((x RDFValue)) (= (exists ((y RDFValue)(z RDFValue)(w RDFValue)) (or (P x y z w) (P y x z w) (P y z x w) (P y z w x))) (f_bound x))))\n";
    
  return res;
}

string tabs(unsigned i) {
  string res;
  for (unsigned j = 0; j < i; j++)
    res += "\t";
  return res;
}

/*
void addAddClausesToAdd(Pattern* p, Pattern* q) {
  if (((And*)q)->numberOfPatterns() != 0) {
    for (auto a : ((And*)q)->getPatterns())
      ((And*)p)->addPattern(a);
  }
  else {
    delete q;
  }
}
*/

string OptionalPattern::formula(unsigned t, set<string> from, set<string> from_named) const {
  string res = tabs(t) + "(or \n";
  
  res += _p->formula(t+1, from, from_named) + "\n";
  
  res += tabs(t+1) + "(forall (";
  for (auto a : _optionalVariables)
    res += "(" + a + " RDFValue)";
  if (_optionalVariables.size() == 0)
    res += "(foo_foo_foo RDFValue)";
  res += ")\n";
  
  res += tabs(t+2) + "(not \n";
  res += _p->formula(t+3, from, from_named) + "\n";
  res += tabs(t+2) + ")\n";
  res += tabs(t+1) + ")\n";
  res += tabs(t) + ")";
  
  return res;
}

string DiffPattern::formula(unsigned t, set<string> from, set<string> from_named) const {
  string res = tabs(t);
  res += "(forall (";
  for (auto a : _optionalVariables)
    res += "(" + a + " RDFValue)";
  if (_optionalVariables.size() == 0)
    res += "(foo_foo_foo RDFValue)";
  res += ")\n";
  
  res += tabs(t+1) + "(not \n";
  res += _p->formula(t+2, from, from_named) + "\n";
  res += tabs(t+1) + ")\n";
  res += tabs(t) + ")";
  
  return res;
}

string MinusPattern::formula(unsigned t, set<string> from, set<string> from_named) const {

  set<string> all = _p->allVariables(getQuery()->getId());
  bool disjunct = true;

  //for (auto a : all)
  //  cout << "all: " << a << endl;

  //for (auto a : _optionalVariables)
  //  cout << "opt: " << a << endl;
  
  for (auto a : all)
    if (!_optionalVariables.count(a))
      disjunct = false;
  if (disjunct == false)  {
    string res = tabs(t);
    res += "(forall (";
    for (auto a : _optionalVariables)
      res += "(" + a + " RDFValue)";
    if (_optionalVariables.size() == 0)
      res += "(foo_foo_foo RDFValue)";
    res += ")\n";
    
    res += tabs(t+1) + "(not \n";
    res += _p->formula(t+2, from, from_named) + "\n";
    res += tabs(t+1) + ")\n";
    res += tabs(t) + ")";
    
    return res;
  }
  else {
    return "";
  }
}

string PrimaryExpression::getString() const {
  return _v->getString();
}

string PrimaryExpression::prepareString(int i, map<string, string> p) {
  if (Variable* tmp = dynamic_cast<Variable*>(_v)) {
    return tmp->prepareString(i);
  }
  if (IRI* tmp = dynamic_cast<IRI*>(_v)) {
    return tmp->prepareString(p);
  }
  cout << "Test" << endl;
  return "";
}

string EqExpression::getString() const {
  return  "(= " + _left->getString() + " " + _right->getString() + ")";
}

string OrExpression::getString() const {
  return  "(or " + _left->getString() + " " + _right->getString() + ")";
}

string AndExpression::getString() const {
  return  "(and " + _left->getString() + " " + _right->getString() + ")";
}

string BuiltinBinExpression::getString() const {
  return  "(" + _name + " " + _left->getString() + " " + _right->getString() + ")";
}

string NotExpression::getString() const {
  return  "(not " + _e->getString() + ")";
}

string BuiltinUnExpression::getString() const {
  return  "(" + _name + " " + _e->getString() + ")";
}

string And::formula(unsigned t, set<string> from, set<string> from_named) const {
  string tt = tabs(t);
  string res = tt;
  res += "(and \n";
  for (auto a : _patterns)
    res += a->formula(t + 1, from, from_named) + "\n";
  res += tt + ")";
  return res;
}

string And::schemaFormula(unsigned t) const {
  string tt = tabs(t);
  string res = tt;
  res += "(and \n";
  for (auto a : _patterns)
    res += a->schemaFormula(t + 1) + "\n";
  res += tt + ")";
  return res;
}

string Union::formula(unsigned t, set<string> from, set<string> from_named) const {
  string tt = tabs(t);
  string res = tt;
  res += "(or \n";
  for (auto a : _patterns)
    res += a->formula(t + 1, from, from_named) + "\n";
  res += tt + ")";
  return res;
}

string Union::schemaFormula(unsigned t) const {
  string tt = tabs(t);
  string res = tt;
  return res;
}

string TriplePattern::formula(unsigned t, set<string> from, set<string> from_named) const {
  string res = tabs(t);
  if (from.size() == 1 && (*from.begin()) == "<default_graph>" && from_named.size() > 0)
    res += "false";
  else if (from.size() > 1) {
    res += "(or ";
    for (auto a : from)
      res += "(P " + _subject->getString() + " "
                   + _predicate->getString() + " "
                   + _object->getString() + " "
                   + a + ") ";
    res += ")";
  }
  else {
    res += "(P " + _subject->getString() + " "
      + _predicate->getString() + " "
      + _object->getString() + " "
      + *from.begin() + ") ";
  }
  return res;
}

string TriplePattern::schemaFormula(unsigned t) const {
  string pred =  _predicate->getString();
  if (pred.find("subClassOf") != string::npos)
    return tabs(t) + "(forall ((x RDFValue)(g RDFValue)) " +
                             "(=> (P x <a> " + _subject->getString() + " g) " +
                               + "(P x <a> " + _object->getString() + " g)))";
  if (pred.find("domain") != string::npos)
        return tabs(t) + "(forall ((x RDFValue)(y RDFValue)(g RDFValue)) " +
	                     "(=> (P x " + _subject->getString() + " y g) " +
                               + "(P x <a> " + _object->getString() + " g)))";
  if (pred.find("range") != string::npos)
        return tabs(t) + "(forall ((x RDFValue)(y RDFValue)(g RDFValue)) " +
	                     "(=> (P x " + _subject->getString() + " y g) " +
                               + "(P y <a> " + _object->getString() + " g)))";
  if (pred.find("subPropertyOf") != string::npos)
        return tabs(t) + "(forall ((x RDFValue)(y RDFValue)(g RDFValue)) " +
                             "(=> (P x " + _subject->getString() + " y g) " +
                               + "(P x " + _object->getString() + " y g)))";
  return "(true)";
}

int Query::_number_of_queries = 1;
map<string, string> Query::_prefixes_abrv;

string Query::formula(unsigned t) const {
  set<string> froms = _from;
  set<string> from_named = _from_named;
  string tmp = _pattern->formula(t, froms, from_named);

  /*
  string tt = tabs(t + 1);
  set<string> graphsVars = _pattern->allGraphVariables();
  set<string> graphs = froms;
  string eq0 = "\t(and \n";
  for (auto a : graphsVars) {
    eq0 += tt + "\t(or ";
    for (auto b : graphs)
      eq0 += "(= " + a + " " + b + ")";
    eq0 += ")\n";
  }
  eq0 += tt + ")\n";
  */
  
  string eq1;
  for (auto p : _projections)
    if (EqExpression* tt1 = dynamic_cast<EqExpression*>(p))
      eq1 = tt1->getString();

  string eq2;
  if (_var != nullptr) {
    EqExpression *eq = new EqExpression(new PrimaryExpression(_var), new PrimaryExpression(_values[0]));
    eq->prepareString(_id, _prefixes_new);
    eq2 = eq->getString();
    delete eq;
  }
  
  tmp = tmp.substr(0, tmp.size()-1);
  if (eq1 != "")
    tmp += "\t" + eq1 + "\n";
  if (eq2 != "")
    tmp += "\t" + eq2 + "\n";
  //tmp += eq0;
  //tmp += tabs(t) + ")";
  tmp += ")";
  
  return tmp;
}

string Query::schemaFormula(unsigned t) const {
  return  _pattern->schemaFormula(t);
}

set<string> Query::projVars() const {
  set<string> res;
  if (!isSelectStar()) {
    for (unsigned i = 0; i < _projections.size(); i++) {
      if (PrimaryExpression* tmp = dynamic_cast<PrimaryExpression*>(_projections[i]))
	res.insert(tmp->getString());
      else if (EqExpression* tmp = dynamic_cast<EqExpression*>(_projections[i]))
	res.insert(tmp->getStringLeft());
      else
	throw "SHOULD NOT HAPPEN";
    }
  }
  else {
    set<string> tmp = allVariables();
    for (auto a : tmp)
      if (a.substr(1,1) != "b")
	res.insert(a);
  }
  return res;
}

string GraphPattern::formula(unsigned t, set<string> from, set<string> from_named) const {
  string tt = tabs(t);
  string res;
  if (Variable* v = dynamic_cast<Variable*>(_v)) {
    res += tt;
    if (from_named.size() == 0 && (from.size() > 1 || (*from.begin()) != "<default_graph>")) {
      res += "false";
    }
    else if (from_named.size() == 0 && from.size() == 1 && (*from.begin()) == "<default_graph>") {
      res += "(exists ((<i_graph> RDFValue))\n";
      set<string> new_from;
      new_from.insert("<i_graph>");
      string tmp;
      if (dynamic_cast<And*>(_p) == nullptr) {
	And* aa = new And();
	aa->addPattern(_p);
	tmp = aa->formula(t + 1, new_from, from_named);
      }
      else {
	tmp = _p->formula(t + 1, new_from, from_named);
      }
      tmp = tmp.substr(0, tmp.size()-1) + tabs(t-1) + "(= " + v->getString() + " <i_graph>)\n" + tt + "\t)";
      res += tmp + "\n";
      res += tt + ")";
    }
    else {
      res += "(or \n";
      for (auto ng : from_named) {
	set<string> new_from;
	new_from.insert(ng);
	string tmp = _p->formula(t + 1, new_from, from_named);
	tmp = tmp.substr(0, tmp.size()-1) + tabs(t-1) + "(= " + v->getString() + " " + ng + ")" + "\n" + tt + "\t)";
	res += tmp;
	res += "\n";
      }
      res += tt + ")\n";
    }
  }
  else {
    if ((from_named.size() != 0 && from_named.count(_v->getString()) == 0)
	|| (from_named.size() == 0 && (from.size() > 1 || (*from.begin()) != "<default_graph>"))) {
      res += tt + "false";
    }
    else {
      set<string> new_from;
      new_from.insert(_v->getString());
      res += _p->formula(t, new_from, from_named);
    }
  }
  return res;
}

string SubqueryPattern::formula(unsigned t, set<string> from, set<string> from_named) const {
  string res;
  res += _q->formula(t);
  res = res.substr(0, res.size()-1) + "\t";

  for (auto a : _q->projVars()) {
    string b = a;
    res += "(= " + b + " " + a.replace(2, 1, to_string(_idOuterQuery)) + ")";
  }
  
  res += "\n\t\t)";
  return res;
}

string eqProj1(const set<string> &super, const set<string> &sub) {
  string res = "(and ";
  for (auto i : super) {
    string tmp1 = i;
    tmp1.replace(1, 2, "");
    for (auto j : sub) {
      string tmp2 = j;
      tmp2.replace(1, 2, "");
      if (tmp1 == tmp2)
	res += "(= " + i + " " + j + ") ";
    }
  }
  res += ")";
  return res;
}

string eqProj2(const set<string> &super, const set<string> &sub) {
  // Zamena super i sub zbog homomorfizma
  set<string> super1 = super;
  set<string> sub1 = sub;
  if (sub1.size() > super1.size()) {
    sub1 = super;
    super1 = sub;
  }
  
  vector<string> tmp(super1.begin(), super1.end());
  vector<vector<string> > comb = variationsWithoutRepetitions(tmp, sub1.size());

  string res = "(or ";
  for (auto i : comb) {
    res += "(and ";
    int k = 0;
    for (auto j : sub1)
      res += "(= " + j + " " + i[k++] + ") ";
    res += ")";
  }
  res += ")";
  return res;
}


string eqProj(const set<string> &super, const set<string> &sub, bool rename) {
  if (rename == false)
    return eqProj1(super, sub);
  
  set<string> super_tmp, sub_tmp;
  for (auto a : super)
    super_tmp.insert(a.replace(1, 2, ""));
  for (auto a : sub)
    sub_tmp.insert(a.replace(1, 2, ""));
  bool same_naming = true;
  for (auto a : sub_tmp)
    if (super_tmp.count(a) == 0) {
      same_naming = false;
      break;
    }
  if (same_naming)
    return eqProj1(super, sub);
  
  return eqProj2(super, sub);
}


/*
string eqProj(const set<string> &super, const set<string> &sub, bool qc) {
  set<string> super_tmp, sub_tmp;
  for (auto a : super)
    super_tmp.insert(a.replace(1, 2, ""));
  for (auto a : sub)
    sub_tmp.insert(a.replace(1, 2, ""));
  bool same_naming = (sub_tmp == super_tmp);
  if (qc) {
    if (!same_naming)
      throw string("Sets of projections in queries are not the same");
  }
  string prefix = super.begin()->substr(1, 2);
  if (same_naming) {
    string res;
    for (auto a : sub) {
      string b = a;
      res += "(= " + b + " " + a.replace(1, 2, prefix) + ") ";
    }
    return res;
  }

  // Zamena super i sub zbog homomorfizma
  set<string> super1 = super;
  set<string> sub1 = sub;
  if (sub1.size() > super1.size()) {
    sub1 = super;
    super1 = sub;
  }
  
  vector<string> tmp(super1.begin(), super1.end());
  vector<vector<string> > comb = variationsWithoutRepetitions(tmp, sub1.size());

  string res = "(or ";
  for (auto i : comb) {
    res += "(and ";
    int k = 0;
    for (auto j : sub1)
      res += "(= " + j + " " + i[k++] + ") ";
    res += ")";
  }
  res += ")";
  return res;
}
*/

extern int counter_iri;
extern map<string, string> old_iris;
string prepareString(const string &t, const map<string, string> &prefixes) {
  size_t size = t.find_first_of(":");
  if (size == string::npos || (t[0] == '<' && t[t.size()-1] == '>')) {
    unsigned xx = t.find_last_of("/#");
    string tt = t.substr(0, xx+1) + ">";
    string pp = t.substr(xx+1, t.size() - xx - 2);
    auto itr = prefixes.find(tt);
    if (itr != prefixes.end() && t.find_first_of("',()") == string::npos) {
      tt = itr->second;
      return tt.replace(tt.find_last_of(">"), 1, pp + ">");
    }
    map<string, string>::iterator tmp = old_iris.find(t);
    if (tmp == old_iris.end())
      return old_iris[t] = "<iri" + to_string(counter_iri++) + ">";
    else
      return tmp->second;
  }
  string prefix = t.substr(0, size);
  string rest =  t.substr(size + 1);
  auto itr = prefixes.find(prefix);
  if (itr == prefixes.end())
    throw "Prefix unknown";
  prefix = itr->second;
  string tmp = prefix.replace(prefix.find_last_of(">"), 1, rest + ">");
  return tmp;
}

void swap(string &v1, string &v2) {
  string old = v1;
  v1 = v2;
  v2 = old;
}

vector<vector<string> > variationsWithoutRepetitions(vector<string> arr, unsigned k) {
  vector<string> tmp(k, "");
  vector<vector<string> > res;
  generateVariationsWithoutRepetitions(arr, k, 0, tmp, res);
  return res;
}

void generateVariationsWithoutRepetitions(vector<string> &arr, unsigned k, unsigned index, vector<string> &tmp, vector<vector<string> > &res) {
  if (index >= k) {
    res.push_back(tmp);
  }
  else {
    for (unsigned i = index; i < arr.size(); i++) {
      tmp[index] = arr[i];
      swap(arr[i], arr[index]);
      generateVariationsWithoutRepetitions(arr, k, index + 1, tmp, res);
      swap(arr[i], arr[index]);
    }
  }
}

Pattern* Union::normalize1() {
  Union *tmp = new Union();
  for (auto &p : _patterns) {
    p = p->normalize1();
    Union* u = dynamic_cast<Union*>(p);
    if (u != nullptr) {
      for (auto a : u->getPatterns())
	tmp->addPattern(a);
    }
    else {
      tmp->addPattern(p);
    }
  }
  if (tmp->getPatterns().size() == 1)
    return tmp->getPatterns()[0];
  return tmp;
}

Pattern* And::normalize1() {
  And *tmp = new And();
  for (auto &p : _patterns) {
    p = p->normalize1();
    And* u = dynamic_cast<And*>(p);
    if (u != nullptr) {
      for (auto a : u->getPatterns())
	tmp->addPattern(a);
    }
    else {
      tmp->addPattern(p);
    }
  }
  if (tmp->getPatterns().size() == 1)
    return tmp->getPatterns()[0];
  return tmp;
}

Pattern* OptionalPattern::normalize() {
  Union* tmp = new Union();
  tmp->addPattern(_p);
  DiffPattern* diff = new DiffPattern(_p);
  diff->setOptionalVariables(_optionalVariables);
  tmp->addPattern(diff);
  return tmp;
}

Pattern* Union::normalize() {
  for (auto &p : _patterns)
    p = p->normalize();
  return this->normalize1();
}

Pattern* And::normalize() {
  for (auto &p : _patterns)
    p = p->normalize();

  Pattern *tmp = _patterns[0];
  for (unsigned i = 1; i < _patterns.size(); i++) {
    Union* u0 = dynamic_cast<Union*>(tmp);
    Union* u1 = dynamic_cast<Union*>(_patterns[i]);
    if (u0 != nullptr && u1 != nullptr) {
      tmp = new Union();
      for (unsigned ii = 0; ii < u0->getPatterns().size(); ii++)
	for (unsigned jj = 0; jj < u1->getPatterns().size(); jj++) {
	  And *tmp1 = new And();
	  tmp1->addPattern(u0->getPatterns()[ii]);
	  tmp1->addPattern(u1->getPatterns()[jj]);
	  ((Union*)tmp)->addPattern(tmp1);
	}
    }
    else if (u0 == nullptr && u1 != nullptr) {
      Union* tmp2 = new Union();
      for (unsigned jj = 0; jj < u1->getPatterns().size(); jj++) {
	And *tmp1 = new And();
	tmp1->addPattern(tmp);
	tmp1->addPattern(u1->getPatterns()[jj]);
	((Union*)tmp2)->addPattern(tmp1);
      }
      tmp = tmp2;
    }
    else if (u0 != nullptr && u1 == nullptr) {
      //tmp = new Union();
      for (unsigned ii = 0; ii < u0->getPatterns().size(); ii++) {
	And *tmp1 = new And();
	tmp1->addPattern(u0->getPatterns()[ii]);
	tmp1->addPattern(_patterns[i]);
	((Union*)tmp)->addPattern(tmp1);
      }      
    }
    else if (u0 == nullptr && u1 == nullptr) {
      And *tmp1 = new And();
      tmp1->addPattern(tmp);
      tmp1->addPattern(_patterns[i]);
      tmp = tmp1;
    }
  }
  
  return tmp->normalize1();
}
