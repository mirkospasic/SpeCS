#ifndef __QUERY_HPP__
#define __QUERY_HPP__ 1

#include <map>
#include <string>
#include <vector>
#include <set>
#include <iostream>
#include "rdf.hpp"
using namespace std;

string common_formula();
string tabs(unsigned i);
string prepareString(const string &t, const map<string, string> &prefixes);

class Query;

/* Basic class for all kind of graph patterns */
class Pattern {
public:
  virtual ~Pattern() {
    
  }
  virtual set<string> allIRIs(map<string, string> prefixes) const = 0;
  virtual set<string> allLiterals() const = 0;
  virtual set<string> allVariables(int i) const = 0;
  virtual set<string> allBoundVariables(int i) const = 0;
  virtual string formula(unsigned t, set<string> from, set<string> from_named) const = 0;
  virtual string schemaFormula(unsigned t) const = 0;
  virtual void setOptionalVariables(set<string> nonOptionalVariables, int i) = 0;
  virtual void setQuery(Query*) = 0;
  virtual Pattern* normalize1() = 0;
  virtual Pattern* normalize() = 0;
  Query* getQuery() const {
    return _qp;
  }
protected:
  Query *_qp;
};

class MorePatterns : public Pattern {
public:
  MorePatterns()
  {
    _patterns.clear();
  }
  vector<Pattern*> getPatterns() const {
    return _patterns;
  }
  ~MorePatterns() {
    for (auto p : _patterns)
      delete p;
  }
  void addPattern(Pattern *p) {
    _patterns.push_back(p);
  }
  set<string> allIRIs(map<string, string> prefixes) const {
    set<string> r;
    for (auto p : _patterns)
      for (auto i : p->allIRIs(prefixes))
	r.insert(i);
    return r;
  }
  set<string> allLiterals() const {
    set<string> r;
    for (auto p : _patterns)
      for (auto i : p->allLiterals())
	r.insert(i);
    return r;
  }
  set<string> allVariables(int i) const {
    set<string> r;
    for (auto p : _patterns)
      for (auto i : p->allVariables(i))
	r.insert(i);
    return r;
  }
  set<string> allBoundVariables(int i) const {
    set<string> r;
    for (auto p : _patterns)
      for (auto i : p->allBoundVariables(i))
	r.insert(i);
    return r;
  }
  void setOptionalVariables(set<string> nonOptionalVariables, int i) {
    for (auto p : _patterns)
      p->setOptionalVariables(nonOptionalVariables, i);
  }
  unsigned numberOfPatterns() const {
    return _patterns.size();
  }
  void setQuery(Query* q) {
    _qp = q;
    for (auto p : _patterns) {
      p->setQuery(q);
    }
  }
protected:
  vector<Pattern*> _patterns;
private:
  MorePatterns(const MorePatterns&);
  MorePatterns& operator=(const MorePatterns &);
};

class And : public MorePatterns {
public:
  And()
    :MorePatterns()
  {}
  string formula(unsigned t, set<string> from, set<string> from_named) const;
  string schemaFormula(unsigned t) const;
  Pattern* normalize1();
  Pattern* normalize();
};

class Union : public MorePatterns {
public:
  Union()
    :MorePatterns()
  {}
  string formula(unsigned t, set<string> from, set<string> from_named) const;
  string schemaFormula(unsigned t) const;
  Pattern* normalize1();
  Pattern* normalize();
};

class TriplePattern : public Pattern {
public:
  TriplePattern(RDFValue *s, RDFValue *p, RDFValue *o)
    :_subject(s), _predicate(p), _object(o)
  {
  }
  ~TriplePattern() {
    delete _subject;
    delete _predicate;
    delete _object;
  }
  set<string> allIRIs(map<string, string> prefixes) const {
    set<string> r;
    if (IRI* tmp = dynamic_cast<IRI*>(_subject)) {
      r.insert(tmp->prepareString(prefixes));
    }
    if (IRI* tmp = dynamic_cast<IRI*>(_predicate)) {
      r.insert(tmp->prepareString(prefixes));
    }
    if (IRI* tmp = dynamic_cast<IRI*>(_object)) {
      r.insert(tmp->prepareString(prefixes));
    }
    return r;
  }
  set<string> allLiterals() const {
    set<string> r;
    //if (Literal* tmp = dynamic_cast<Literal*>(_subject)) {
    //  r.insert(tmp->prepareString());
    //}
    if (Literal* tmp = dynamic_cast<Literal*>(_predicate)) {
      r.insert(tmp->prepareString());
    }
    if (Literal* tmp = dynamic_cast<Literal*>(_object)) {
      r.insert(tmp->prepareString());
    }
    return r;
  }
  set<string> allVariables(int i) const {
    set<string> r;
    if (Variable* tmp = dynamic_cast<Variable*>(_subject)) {
      r.insert(tmp->prepareString(i));
    }
    if (Variable* tmp = dynamic_cast<Variable*>(_predicate)) {
      r.insert(tmp->prepareString(i));
    }
    if (Variable* tmp = dynamic_cast<Variable*>(_object)) {
      r.insert(tmp->prepareString(i));
    }
    if (BlankNode* tmp = dynamic_cast<BlankNode*>(_subject)) {
      r.insert(tmp->prepareString(i));
    }
    if (BlankNode* tmp = dynamic_cast<BlankNode*>(_predicate)) {
      r.insert(tmp->prepareString(i));
    }
    if (BlankNode* tmp = dynamic_cast<BlankNode*>(_object)) {
      r.insert(tmp->prepareString(i));
    }
    return r;
  }
  set<string> allBoundVariables(int i) const {
    return allVariables(i);
  }
  void setOptionalVariables(set<string> nonOptionalVariables, int i) {
    //NOTHING
  }
  string formula(unsigned t, set<string> from, set<string> from_named) const;
  string schemaFormula(unsigned t) const;
  void setQuery(Query* q) {
    _qp = q;
  }
  Pattern* normalize1() { return this;}
  Pattern* normalize() { return this;}
private:
  RDFValue* _subject;
  RDFValue* _predicate;
  RDFValue* _object;
};

class OptionalPattern : public Pattern {
public:
  OptionalPattern(Pattern *p)
    :_p(p)
  {  }
  ~OptionalPattern() {
    delete _p;
  }
  set<string> allIRIs(map<string, string> prefixes) const {
    return _p->allIRIs(prefixes);
  }
  set<string> allLiterals() const {
    return _p->allLiterals();
  }
  set<string> allVariables(int i) const {
    return _p->allVariables(i);
  }
  set<string> allBoundVariables(int i) const {
    return set<string>();
  }
  void setOptionalVariables(set<string> nonOptionalVariables, int i) {
    for (auto v : allVariables(i)) {
      if (nonOptionalVariables.count(v) == 0)
	_optionalVariables.insert(v);
    }
  }
  string formula(unsigned t, set<string> from, set<string> from_named) const;
  string schemaFormula(unsigned t) const {
    //Should not happen
    return "";
  }
  void setOptionalVariables(set<string> optionalVariables) {
    _optionalVariables = optionalVariables;
  }
  void setQuery(Query* q) {
    _qp = q;
    _p->setQuery(q);
  }
  Pattern* normalize1() { return this; }
  Pattern* normalize();
private:
  OptionalPattern(const OptionalPattern&);
  OptionalPattern& operator=(const OptionalPattern&);
protected:
  Pattern *_p;
  set<string> _optionalVariables;
};

class MinusPattern : public OptionalPattern {
public:
  MinusPattern(Pattern *p)
    :OptionalPattern(p)
  {  }
  string formula(unsigned t, set<string> from, set<string> from_named) const;
};


class Expression : public Pattern {
public:
  virtual string getString() const = 0;
  virtual string prepareString(int i, map<string, string> p) = 0;
  string schemaFormula(unsigned t) const {
    throw "Schema cannot have expressions";
  }
  string formula(unsigned t, set<string> from, set<string> from_named) const {
    return tabs(t) + getString();
  }
  set<string> allBoundVariables(int i) const {
    return set<string>();
  }
  void setOptionalVariables(set<string> nonOptionalVariables, int i) {
    // NOTHING
  }
  void setQuery(Query* q) {
    _qp = q;
  }
  Pattern* normalize1() { return this; }
  Pattern* normalize() { return this; }
};

class PrimaryExpression : public Expression {
public:
  PrimaryExpression(RDFValue* v)
    :_v(v)
  {}
  string getString() const;
  string prepareString(int i, map<string, string> p);
  set<string> allIRIs(map<string, string> prefixes) const {
    set<string> r;
    if (IRI* tmp = dynamic_cast<IRI*>(_v)) {
      r.insert(tmp->prepareString(prefixes));
    }
    return r;
  }
  set<string> allLiterals() const {
    set<string> r;
    if (Literal* tmp = dynamic_cast<Literal*>(_v)) {
      r.insert(tmp->prepareString());
    }
    return r;
  }
  set<string> allVariables(int i) const {
    set<string> r;
    if (Variable* tmp = dynamic_cast<Variable*>(_v)) {
      r.insert(tmp->prepareString(i));
    }
    return r;
  }
private:
  RDFValue* _v;
};

class BinExpression : public Expression {
public:
  BinExpression(Expression *l, Expression *r)
    :_left(l), _right(r)
  {}
  ~BinExpression() {
    delete _left;
    delete _right;
  }
  set<string> allIRIs(map<string, string> prefixes) const {
    set<string> res = _left->allIRIs(prefixes);
    set<string> tmp = _right->allIRIs(prefixes);
    res.insert(tmp.begin(), tmp.end());
    return res;
  }
  set<string> allLiterals() const {
    set<string> res = _left->allLiterals();
    set<string> tmp = _right->allLiterals();
    res.insert(tmp.begin(), tmp.end());
    return res;
  }
  set<string> allVariables(int i) const {
    set<string> res = _left->allVariables(i);
    set<string> tmp = _right->allVariables(i);
    res.insert(tmp.begin(), tmp.end());
    return res;
  }
  string prepareString(int i, map<string, string> p)  {
    _left->prepareString(i, p);
    _right->prepareString(i, p);
    return "";
  }
protected:
  Expression *_left, *_right;
private:
  BinExpression(const BinExpression&);
  BinExpression& operator=(const BinExpression&);
};

class UnExpression : public Expression {
public:
  UnExpression(Expression *e)
    :_e(e)
  {}
  ~UnExpression() {
    delete _e;
  }
  set<string> allIRIs(map<string, string> prefixes) const {
    return _e->allIRIs(prefixes);
  }
  set<string> allLiterals() const {
    return _e->allLiterals();
  }
  set<string> allVariables(int i) const {
    return _e->allVariables(i);
  }
  string prepareString(int i, map<string, string> p)  {
    _e->prepareString(i, p);
    return "";
  }
protected:
  Expression *_e;
private:
  UnExpression(const UnExpression&);
  UnExpression& operator=(const UnExpression&);
};

class EqExpression : public BinExpression {
public:
  EqExpression(Expression *l, Expression *r)
    :BinExpression(l, r)
  {}
  string getString() const;
  string getStringLeft() const {
    return _left->getString();
  }
};

class OrExpression : public BinExpression {
public:
  OrExpression(Expression *l, Expression *r)
    :BinExpression(l, r)
  {}
  string getString() const;
};

class AndExpression : public BinExpression {
public:
  AndExpression(Expression *l, Expression *r)
    :BinExpression(l, r)
  {}
  string getString() const;
};

class BuiltinBinExpression : public BinExpression {
public:
  BuiltinBinExpression(string n, Expression *l, Expression *r)
    :BinExpression(l, r), _name(n)
  {}
  string getString() const;
private:
  string _name;
};

class NotExpression : public UnExpression {
public:
  NotExpression(Expression *e)
    :UnExpression(e)
  {}
  string getString() const;
};

class BuiltinUnExpression : public UnExpression {
public:
  BuiltinUnExpression(string n, Expression *e)
    :UnExpression(e), _name(n)
  {}
  string getString() const;
private:
  string _name;
};


/* Class representing a single SPARQL query  */
class Query {
public:
  Query(map<string, string> m, vector<Expression*> v, Pattern* p, pair<set<string>, set<string> > f = pair<set<string>, set<string> >(set<string>(), set<string>()), int l = -1, int o = -1, RDFValue* var = nullptr, vector<RDFValue*> values = vector<RDFValue*>())
    :_prefixes(m), _projections(v), _pattern(p), _from(f.first), _from_named(f.second), _limit(l), _offset(o), _var(var), _values(values)
  {
    for (auto a : _prefixes) {
      if (_prefixes_abrv[a.second] == "")
	_prefixes_abrv[a.second] = "<p" + to_string(_prefixes_abrv.size()) + "_>";
    }
    _id = _number_of_queries++;

    for (auto a : _prefixes)
      _prefixes_new[a.first] = _prefixes_abrv[a.second];
    _prefixes_new.insert(_prefixes_abrv.begin(), _prefixes_abrv.end());
    
    for (auto a : _projections)
      a->prepareString(_id, _prefixes_new);

    set<string> res;
    for (auto a : _from) {
      res.insert(prepareString(a, _prefixes_new));
    }
    _from = res;
    set<string> res1;
    for (auto a : _from_named) {
      res1.insert(prepareString(a, _prefixes_new));
    }
    _from_named = res1;
    
    set<string> tmp = _pattern->allBoundVariables(_id);
    p->setOptionalVariables(tmp, _id);

    _pattern->setQuery(this);
    
    if (_from.size() == 0)
      _from.insert("<default_graph>");
    
  }
  void addCommonPrefixes() {
    _prefixes_new.insert(_prefixes_abrv.begin(), _prefixes_abrv.end());
  }
  set<string> allIRIs() const {
    set<string> res = _pattern->allIRIs(_prefixes_new);
    for (auto a : _values) {
      res.insert(((IRI*)a)->prepareString(_prefixes_new));
    }
    return res;
  }
  set<string> allLiterals() const {
    return _pattern->allLiterals();
  }
  set<string> allVariables() const {
    set<string> res = _pattern->allVariables(_id);
    for (auto a : _projections) {
      set<string> tmp = a->allVariables(_id);
      res.insert(tmp.begin(), tmp.end());
    }
    return res;
  }
  ~Query() {
    for (auto a : _projections)
      delete a;
    delete _pattern;
  }
  string formula(unsigned t) const;
  string schemaFormula(unsigned t) const;
  vector<Expression*> getProjections() const {
    return _projections;
  }
  bool isSelectStar() const {
    return _projections.size() == 0;
  }
  set<string> projVars() const;
  int getLimit() const {
    return _limit;
  }
  int getOffset() const {
    return _offset;
  }
  set<string> getFrom() const {
    return _from;
  }
  set<string> getFromNamed() const {
    return _from_named;
  }
  void setPrefixesNew(const map<string, string> &m) {
    _prefixes_new = m;
  }
  int getId() const {
    return _id;
  }
  Pattern* getPattern() const {
    return _pattern;
  }
  void setQuery(Query* q) {
    _pattern->setQuery(q);
  }
  void normalize() {
    _pattern = _pattern->normalize1();
    _pattern = _pattern->normalize();  
    And* tmp = dynamic_cast<And*>(_pattern);
    if (tmp == nullptr) {
      And *a = new And();
      a->addPattern(_pattern);
      _pattern = a;
    }
  }
  unsigned numberOfConjuctive() const {
    Union* tmp = dynamic_cast<Union*>(((And*)(_pattern))->getPatterns()[0]);
    if (tmp == nullptr)
      return 1;
    else
      return tmp->getPatterns().size();
  }
  Query* i_th_query(unsigned i) const {
    Query* q_i = new Query(*this);
    if (numberOfConjuctive() == 1)
      return q_i;
    Union* tmp = dynamic_cast<Union*>(((And*)(_pattern))->getPatterns()[0]);
    if (dynamic_cast<And*>(tmp->getPatterns()[i]) == nullptr) {
      And *a = new And();
      a->addPattern(tmp->getPatterns()[i]);
      q_i->_pattern = a;
    }
    else
      q_i->_pattern = tmp->getPatterns()[i];
    return q_i;
  }
private:
  map<string, string> _prefixes;
  map<string, string> _prefixes_new;
  static map<string, string> _prefixes_abrv;
  vector<Expression*> _projections;
  Pattern* _pattern;
  set<string> _from;
  set<string> _from_named;
  int _limit;
  int _offset;
  RDFValue* _var;
  vector<RDFValue*> _values;
  static int _number_of_queries;
  int _id;
};

class SubqueryPattern : public Pattern {
public:
  SubqueryPattern(Query *q)
    :_q(q)
  {  }
  ~SubqueryPattern() {
    delete _q;
  }
  set<string> allIRIs(map<string, string> prefixes) const {
    _q->setPrefixesNew(prefixes);
    return _q->allIRIs();
  }
  set<string> allLiterals() const {
    return _q->allLiterals();
  }
  set<string> allVariables(int i) const {
    set<string> res = _q->getPattern()->allVariables(_q->getId());
    for (auto a : _q->projVars()) {
      res.insert(a.replace(2, 1, to_string(i)));
    }
    return res;
  }
  set<string> allBoundVariables(int i) const {
    return _q->getPattern()->allBoundVariables(_q->getId());
  }
  void setOptionalVariables(set<string> nonOptionalVariables, int i) {
    _idOuterQuery = i;
  }
  string formula(unsigned t, set<string> from, set<string> from_named) const;
  string schemaFormula(unsigned t) const {
    //Should not happen
    return "";
  }
  void setQuery(Query* q) {
    _qp = q;
    _q->setQuery(q);
  }
  Pattern* normalize1() { _q->normalize(); return this; }
  Pattern* normalize() { _q->normalize(); return this; }
private:
  SubqueryPattern(const SubqueryPattern&);
  SubqueryPattern& operator=(const SubqueryPattern&);
  Query *_q;
  int _idOuterQuery;
};

class GraphPattern : public Pattern {
public:
  GraphPattern(RDFValue *v, Pattern *p)
    :_v(v), _p(p)
  {  }
  ~GraphPattern() {
    delete _v;
    delete _p;
  }
  set<string> allIRIs(map<string, string> prefixes) const {
    set<string> tmp = _p->allIRIs(prefixes);
    if (IRI* iri = dynamic_cast<IRI*>(_v))
      tmp.insert(iri->prepareString(prefixes));
    return tmp;		 
  }
  set<string> allLiterals() const {
    return _p->allLiterals();
  }
  set<string> allVariables(int i) const {
    set<string> res = _p->allVariables(i);
    if (Variable* v = dynamic_cast<Variable*>(_v))
      res.insert(v->prepareString(i));
    return res;
  }
  set<string> allBoundVariables(int i) const {
    return _p->allBoundVariables(i);
  }
  void setOptionalVariables(set<string> nonOptionalVariables, int i) {
    // NOTHING
  }
  string formula(unsigned t, set<string> from, set<string> from_named) const;
  string schemaFormula(unsigned t) const {
    //Should not happen
    return "";
  }
  void setQuery(Query* q) {
    _p->setQuery(q);
  }
  Pattern* normalize1() { _p = _p->normalize1(); return this; }
  Pattern* normalize() { _p = _p->normalize(); return this; }
private:
  GraphPattern(const GraphPattern&);
  GraphPattern& operator=(const GraphPattern&);
  RDFValue *_v;
  Pattern *_p;
};


void addAddClausesToAdd(Pattern* p, Pattern* q);
string eqProj1(const set<string> &super, const set<string> &sub);
string eqProj2(const set<string> &super, const set<string> &sub);
string eqProj(const set<string> &a, const set<string> &b, bool qc);
void swap(string &v1, string &v2);
vector<vector<string> > variationsWithoutRepetitions(vector<string> arr, unsigned k);
void generateVariationsWithoutRepetitions(vector<string> &arr, unsigned k, unsigned index, vector<string> &tmp, vector<vector<string> > &res);

#endif
