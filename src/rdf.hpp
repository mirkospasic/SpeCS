#ifndef __RDF_HPP__
#define __RDF_HPP__ 1

#include <string>
#include <map>
using namespace std;

/* Basic class for all SPARQL IRIs, variables, blank nodes and literals */
class RDFValue {
public:
  virtual ~RDFValue() {

  }
  virtual RDFValue* clone() const = 0;
  string getString() const {
    return _str;
  }
protected:
  string _str;
};

class IRI : public RDFValue {
public:
  IRI(string i)
    :_iri(i)
  {}
  string prepareString(const map<string, string> &prefixes);
  RDFValue* clone() const {
    return new IRI(_iri);
  }
  string getIri() const {
    return _iri;
  }
private:
  string _iri;
};

class Variable : public RDFValue {
public:
  Variable(string v)
    :_var(v)
  {}
  RDFValue* clone() const {
    return new Variable(_var);
  }
  string prepareString(int i);
protected:
  string _var;
};


class Literal : public RDFValue {
public:
  Literal(string l)
    :_lit(l)
  {}
  RDFValue* clone() const {
    return new Literal(_lit);
  }
  string prepareString();
private:
  string _lit;
};

class BlankNode : public RDFValue {
public:
  BlankNode(string b)
    :_name(b)
  {}
  RDFValue* clone() const {
    return new BlankNode(_name);
  }
  string prepareString(int i);
private:
  string _name;
};


#endif
