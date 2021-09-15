#include "domain.hpp"
#include "parsetree.hpp"
#include "tworegularize.hpp"
#include "util.hpp"
#include <iostream>
#include <algorithm>
using namespace std;

void tail_rekursion(method & m) {
    if (m.ps.size() <= 2) { // Base case
        methods.push_back(m);
        return;
    }

    task tail_task;
    string method_prefix="_two_reg_method";
    string prefix = "_two_reg_task";
    string suffix = m.name;
    int count = 0;
    if (equal(method_prefix.begin(), method_prefix.end(), suffix.begin())) { // To avoid a linear increase of the prefix
        size_t pos = suffix.find("__");
        size_t pos2 = pos-1;
        while (pos2 > 0 && isdigit(suffix[pos2])) pos2--; // gets the count of the previous prefix
        count = stoi(suffix.substr(pos2+1, pos-pos2-1))+1;
        suffix = suffix.substr(pos+2, string::npos);
    }
    while (task_name_map.find(prefix + to_string(count) + "__" + suffix) != task_name_map.end()) count++;
    tail_task.name = prefix + to_string(count) + "__" + suffix;

    set<string> head_args;
    set<string> tail_args;
    set<string> tail_task_args;
    for (auto it = m.ps.begin()+1; it != m.ps.end(); it++)
        for (auto p : it->args)
            tail_args.insert(p);
    set<string> atargs; for (auto a : m.atargs) atargs.insert(a);
    set<string> min_ps_args; for (auto a : m.ps[0].args) min_ps_args.insert(a);

    vector<pair<string, string>> head_vars;
    vector<pair<string, string>> tail_vars;
    for (auto p : m.vars) {
        if (tail_args.count(p.first))
            tail_vars.push_back(p); 
        // Check if var in head method's parameter args
        if (atargs.count(p.first)) {
            if (tail_args.count(p.first)) {
                tail_task.vars.push_back(p);
                tail_task_args.insert(p.first);
            }
            head_vars.push_back(p);
            head_args.insert(p.first);
        // Check if var in local args of minimal task
        } else if (min_ps_args.count(p.first)) {
            if (tail_args.count(p.first)) {
                tail_task.vars.push_back(p);
                tail_task_args.insert(p.first);
            }
            head_vars.push_back(p);
            head_args.insert(p.first);
        }
    }

    vector<literal> head_constraints;
    vector<literal> tail_constraints;
    for (auto l : m.constraints) {
        bool in_head=false, in_tail=false;
        for (auto a : l.arguments) { // Check which variables a literal uses
            if (!in_head && min_ps_args.count(a)) // Every variable either appears in the head, tail or both
                in_head=true;
            if (!in_tail && tail_args.count(a))
                in_tail=true;
            if (in_head && in_tail)
                break;
        }
        if (in_head) { // A constraint uses variables of the head
            head_constraints.push_back(l);
            if (in_tail) { // If a constraint-variable is in the tail, then pull it up to the tail task
                set<string> arguments; for (auto a : l.arguments) arguments.insert(a);
                for (auto p : m.vars)
                    if (arguments.count(p.first) && tail_args.count(p.first) && !tail_task_args.count(p.first)) {
                        tail_task.vars.push_back(p);
                        tail_task_args.insert(p.first);
                        if (!head_args.count(p.first)) {
                            head_vars.push_back(p);
                            head_args.insert(p.first);
                        }
                    }
            }
        } else // All vars used in the constraint are of the tail if none are of the head, since every var is in at leat one place
            tail_constraints.push_back(l);
    }
    
    tail_task.number_of_original_vars = (int)tail_task.vars.size();
    tail_task.constraints.clear();
    tail_task.costExpression.clear();
    tail_task.artificial = true;
    abstract_tasks.push_back(tail_task);
    task_name_map[tail_task.name] = tail_task;
        
    plan_step tail_step;
    tail_step.task = tail_task.name;
    tail_step.id = m.ps[1].id;
    for (auto [var,_] : tail_task.vars) tail_step.args.push_back(var);

    method head;
    head.name = m.name;
    head.vars = head_vars;
    head.at = m.at;
    head.atargs = m.atargs;
    head.ps = {m.ps[0], tail_step};
    head.constraints = head_constraints;
    head.ordering = {{m.ps[0].id, tail_step.id}};
    methods.push_back(head);

    method tail;
    tail.name = method_prefix + to_string(count) + "__" + suffix;
    tail.vars = tail_vars;
    tail.at = tail_task.name;
    tail.atargs = tail_step.args;
    tail.ps = m.ps;
    tail.ps.erase(tail.ps.begin());
    tail.constraints = tail_constraints;
    tail.ordering = m.ordering;
    tail.ordering.erase(tail.ordering.begin());

#ifndef NDEBUG
    tail_task.check_integrity();
    tail.check_integrity();
    head.check_integrity();
#endif

    tail_rekursion(tail);
}

void two_regularize_methods() {
#ifndef NDEBUG
    cout << "OLD METHODS:" << endl;
    for (method m : methods)
        cout << "name: " << m.name << ", size: " << m.ps.size() << endl;
#endif

    vector<method> old = methods;
    methods.clear();
    for (method m : old) {
        if (m.ps.size() <= 2) {
            methods.push_back(m);
            continue;
        }

        sort(m.ps.begin(), m.ps.end(), [&](const plan_step & k, const plan_step & l) { return m.is_smaller(k ,l); });
        vector<pair<string,string>> simplefied_ordering;
        for (size_t j = 0; j < m.ps.size()-1; j++) {
            if (!m.is_smaller(m.ps[j], m.ps[j+1]))
                break;
            simplefied_ordering.push_back({m.ps[j].id, m.ps[j+1].id});
        }
        if (simplefied_ordering.size() != m.ps.size()-1) {
            methods.push_back(m);
            continue;
        }

        m.ordering = simplefied_ordering;
        tail_rekursion(m);
    }

#ifndef NDEBUG
    cout << "NEW METHODS:" << endl;
    for (method m : methods)
        cout << "name: " << m.name << ", size: " << m.ps.size() << endl;
#endif
}
