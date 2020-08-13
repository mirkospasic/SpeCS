#include "rdf.hpp"

int counter_iri = 0;
map<string, string> old_iris;
string IRI::prepareString(const map<string, string> &prefixes) {
  if (_iri == "a" || _iri == "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>")
    return _str = "<a>";
  size_t size = _iri.find_first_of(":");
  if (size == string::npos || (_iri[0] == '<' && _iri[_iri.size()-1] == '>')) {
    unsigned xx = _iri.find_last_of("/#");
    string tt = _iri.substr(0, xx+1) + ">";
    string pp = _iri.substr(xx+1, _iri.size() - xx - 2);
    auto itr = prefixes.find(tt);
    if (itr != prefixes.end() && _iri.find_first_of("',()") == string::npos) {
      tt = itr->second;
      return _str = tt.replace(tt.find_last_of(">"), 1, pp + ">");
    }
    map<string, string>::iterator tmp = old_iris.find(_iri);
    if (tmp == old_iris.end()) 
      return _str = old_iris[_iri] = "<iri" + to_string(counter_iri++) + ">";
    else
      return _str = tmp->second;
  }
  string prefix = _iri.substr(0, size);
  string rest =  _iri.substr(size + 1);
  auto itr = prefixes.find(prefix);
  if (itr == prefixes.end())
    throw "Prefix unknown";
  prefix = itr->second;
  return _str = prefix.replace(prefix.find_last_of(">"), 1, rest + ">");
}

int counter_str = 0;
map<string, string> old_strs;
string Literal::prepareString() {
  if (_lit[0] == '"') {
    map<string, string>::iterator tmp = old_strs.find(_lit);
    if (tmp == old_strs.end()) {
      return _str = old_strs[_lit] = "<l_" + to_string(counter_str++) + ">";
    }
    else
      return _str = tmp->second;
  }
  else
    return _str = "<l_" + _lit + ">";
}

string Variable::prepareString(int i) {
  string v = _var;
  return _str = "<" + v.replace(0, 1, "v" + to_string(i) + "_") + ">";
}


string BlankNode::prepareString(int i) {
  return _str = "<b" + to_string(i) + "_" + _name.substr(2) + ">";
}
