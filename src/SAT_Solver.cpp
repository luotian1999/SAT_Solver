#include <iostream>
#include <vector>
#include <tuple>
#include <algorithm>
#include <string.h>
#include <cmath>
using namespace std;

typedef tuple<bool,int> literal; //not satisfied/not yet satisfied, var
typedef tuple<int,int,int,vector<literal>> clause; //satisfied/not satisfied, num_vars, next, literal vec
typedef tuple<int,int,vector<clause>> formula; //minimum, clauses,literal vec


bool cmp(literal i, literal j){
   return abs(get<1>(i)) < abs(get<1>(j));
}


void print_clause(clause const &c){
  cout << "Satisfied by: " << get<0>(c) << "\nNumber of literals left: " << get<1>(c);
  cout << "\nNext literal index: " << get<2>(c) << "\nClause: ";
  vector<literal> l = get<3>(c);
  int l_size = l.size();
  for(int i = 0; i < l_size; i++){
    cout << "(" << get<0>(l[i]) << "," << get<1>(l[i]) << ")";
  }
  cout << "\n";
}

void print_c(clause const &c){
  if(get<0>(c) > 0){
    return;
  }
  vector<literal> l = get<3>(c);
  int l_size = l.size();
  cout << "(";
  bool first = false;
  for(int i = 0; i < l_size; i++){
    if(!get<0>(l[i])){
        continue;
    }
    if(first){
      cout << " ";
    }
    first = true;
    cout << get<1>(l[i]);
  }
  cout << ")";
}

void print_formula(formula &CNF){
  vector<clause> &f = get<2>(CNF);
  int c = f.size();
  for(int i = 0; i < c; i++){
    print_c(f.at(i));
  }
  cout << "\n";
}




void print_vec(vector<char> &v_arr, int var)
{
  if(var < 0){
    v_arr[-var-1] = '-';
  }
  else{
    v_arr[var-1] = '+';
  }
  int s = v_arr.size();
  for (int i = 0; i < s; i++) {
    cout << v_arr[i] << ' ';
  }
  cout << "\n";
}


void print_CNF(formula &CNF){
  vector<clause> &f = get<2>(CNF);
  int c = f.size();
  for(int i = 0; i < c; i++){
    print_clause(f.at(i));
  }
  cout << "\n";
}


void find_next(clause &c){
  int &next = get<2>(c);
  vector<literal> &c_arr = get<3>(c);
  int c_s = c_arr.size();
  while(get<0>(c_arr[next]) == 0 && next < c_s){
    next++;
  }
  return;
}

int set(formula &CNF, int var, int n){
  int num_sat = 0;
  vector<clause> &f = get<2>(CNF);
  int num_c = f.size();
  int min_c = n, min_ind = 0;
  int ret = get<0>(CNF);

  for(int i = 0; i < num_c; i++){
    clause &c = f[i];
    if(get<0>(c) == 0) {
      vector<literal> &c_arr = get<3>(c);
      int c_s = c_arr.size();
      for(int j = 0; j < c_s; j++) {
        int c_j = get<1>(c_arr[j]);
        if(c_j == var){
          get<0>(c) = var;
          num_sat++;
          break;
        }
        if(c_j == -var){
          get<0>(c_arr[j]) = 0;
          get<1>(c)--;
          break;
        }
      }
      find_next(c);
      if(get<1>(c) < min_c && get<0>(c) == 0){
        min_c = get<1>(c);
        min_ind = i;
      }
    }
  }
  get<1>(CNF) -= num_sat;
  get<0>(CNF) = min_ind;
  return ret;
}

void reset(formula &CNF, int var, int n, int ret){
  int num_sat = 0;
  vector<clause> &f = get<2>(CNF);
  int num_c = f.size();
  int min_c = n, min_ind = 0, min_vind = n;

  for(int i = 0; i < num_c; i++){
    clause &c = f[i];
    min_vind = get<2>(c);
    if(get<0>(c) == var) {
      get<0>(c) = 0;
      num_sat++;
    }
    else if(get<0>(c) == 0) {
      vector<literal> &c_arr = get<3>(c);
      int c_s = c_arr.size();
      for(int j = 0; j < c_s; j++) {
        int c_j = get<1>(c_arr[j]);
        if(c_j == -var){
          if(j < min_vind){
            min_vind = j;
          }
          get<0>(c_arr[j]) = 1;
          get<1>(c)++;
          break;
        }
      }
      //if(get<1>(c) < min_c){
      //  min_c = get<1>(c);
      //  min_ind = i;
      //}
    }
    get<2>(c) = min_vind;
  }
  get<1>(CNF) += num_sat;
  get<0>(CNF) = ret;
  return;
}

//recursive_SAT(formula &CNF, int n, bool vtrace, bool ctrace, vector<char> &v_arr){




//}




bool solve_SAT(formula &CNF, int n, bool vtrace, bool ctrace, vector<char> &v_arr){
  if(get<1>(CNF) == 0){
    return true;
  }
  clause &c = (get<2>(CNF))[get<0>(CNF)];
  if(get<1>(c) == 0 && get<0>(c) == 0){
    return false;
  }
  vector<int> vars;
  bool first = true;
  int retf;
  while(get<1>(c) > 0){
    literal &v = (get<3>(c))[get<2>(c)];
    int var = get<1>(v);
    int ret = set(CNF, var, n);
    if(vtrace){
      print_vec(v_arr, var);
    }
    if(ctrace){
      print_formula(CNF);
    }
    //cout << var << "\n";
    //print_CNF(CNF);
    if(solve_SAT(CNF,n, vtrace, ctrace, v_arr)){
      return true;
    }
    else{
      reset(CNF, var, n, ret);
      if(first){
        retf = set(CNF,-var,n);
      }
      else{
        set(CNF, -var, n);
      }
      vars.push_back(-var);
      if(vtrace){
        print_vec(v_arr, -var);
      }
      if(ctrace){
        print_formula(CNF);
      }
    }
  }
  int s = vars.size();
  for(int i = 0; i < s; i++){
    reset(CNF, vars.back(), n, retf);
    vars.pop_back();
  }

  return false;

}

int find_taut(vector<literal>& literals, int target){
  int s = literals.size();
  for(int i = 0; i < s; i++){
    int var = get<1>(literals[i]);
    if(var == target){
      return 1;
    }
    if(var == -target){
      return 2;
    }
  }
  return 0;
}



int main (int argc, char **argv)
{
    int num_vars, num_clauses, num_literals, check, var;
    char word[100];
    bool cont = true;
    bool vtrace = false, ctrace = false;

    for(int i = 0; i < argc; i++)
    {
      if(strcmp(argv[i], "-c") == 0){
        ctrace = true;
      }
      else if(strcmp(argv[i],"-v") == 0){
        vtrace = true;
      }
    }

    while(cont){
      while(strcmp(word,"p") != 0){
        cin >> word;
      }
      cin >> word;
      if(strcmp(word,"cnf") == 0){
        cont = false;
      }
    }


    cin >> num_vars;
    cin >> num_clauses;
    vector<clause> clauses;
    vector<char> variables;
    int num_unsat = 0;
    int min_ind = 0, min_lits = num_vars;

    if(vtrace){
      variables = vector<char>(num_vars,'.');
    }

    for(int i = 0; i < num_clauses; i++){ //iterate over clauses
      bool taut = 0;
      int nth;
      num_literals = 0;
      //cin >> num_literals;
      int same = 0;
      vector<literal> literals;
      cin >> var;
      while(var != 0){
      //for(int j = 0; j < num_literals; j++){ //iterate over literals in clauses
        //cin >> var;
        check = find_taut(literals, var);
        if(check == 2){
          taut = 1;
        }
        if(check == 0){
          literal l = make_tuple(1,var);
          literals.push_back(make_tuple(1,var));
          num_literals++;
        }
        if(check == 1){
         // same++;
        }
        cin >> var;
      }
      //cin >> nth;
      if(!taut){
        num_unsat++;
      }
      if(num_literals < min_lits) {
        min_lits = num_literals;
        min_ind = i;
      }
      if(vtrace || ctrace){
        sort(literals.begin(), literals.end(), cmp);
      }
      clause x = make_tuple(taut,num_literals-same,0,literals);
      clauses.push_back(x);
    }
    formula CNF = make_tuple(min_ind,num_unsat, clauses);
    //print_CNF(CNF);
    cout << "\n";
    if(vtrace){
      for(int i = 0; i < num_vars; i++){
        cout << ". ";
      }
      cout << "\n";
    }
    if(ctrace){
      print_formula(CNF);
    }

    bool SAT = solve_SAT(CNF,num_vars,vtrace, ctrace, variables);

    if(ctrace || vtrace){
      cout << "\n";
    }

    if(SAT){
      cout << "Satisfiable" << "\n";
      if(vtrace){
        for(int i = 0; i < num_vars; i++){
          cout << variables[i] << " ";
        }
        cout << "\n";
      }
    }
    else {
      cout << "Unsatisfiable" << "\n";
    }



    return 0;
}



