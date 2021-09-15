#include "domain.hpp"
#include "parsetree.hpp"
#include "inference.hpp"
#include "util.hpp"
#include <iostream>
#include <algorithm>

using namespace std;


// Statistics
map<string, pair<size_t, size_t>> method_inferences;

void print_statistics() {
    size_t total_inferences = 0;
    size_t total_redundant_inferences = 0;
    size_t total_inference_methods = 0;
    size_t total_methods = methods.size();
    size_t total_tasks = abstract_tasks.size() + primitive_tasks.size();
    for (auto [name, pi] : method_inferences) {
        if (pi.first != 0) {
            total_inference_methods++;
        }
        total_inferences += pi.first;
        total_redundant_inferences += pi.second;
    }

    cout << "Inference Statistics: ";

    auto total_inf = total_redundant_inferences + total_inferences;
    if (total_inf == 0)
        cout << 0 << " ";
    else
        cout << (double)total_redundant_inferences / total_inf << " ";

    cout << (double)total_inferences / total_methods << " ";
    cout << (double)total_inference_methods / total_methods << " ";

    cout << (double)total_inferences / total_tasks << " ";
    cout << (double)total_inference_methods / total_tasks << " ";

    cout << (double)total_inferences / (total_methods + total_tasks) << " ";
    cout << (double)total_inference_methods / (total_methods + total_tasks) << " ";

    cout << total_inferences << " ";
    cout << total_inference_methods << " ";

    cout << total_methods << " ";
    cout << total_tasks << endl;
}


// Main code
typedef string arg_t;
typedef vector<arg_t> sig_t;
typedef vector<sig_t> inf_t;

inf_t ALL = {{"__ALL__"}};

struct data_t {
    bool init = false;
    bool finished = false;
    inf_t non_empty = {};
    inf_t add_non_empty = {};
    inf_t add_reachable = {};
};

map<string, data_t> task_data;

void print_sig(sig_t & sig) {
    for (auto arg : sig) {
        cout << arg << " ";
    }
    cout << endl;
}

void print_inf(inf_t & inf, bool full) {
    int i = 0;
    for (auto sig : inf) {
        cout << i << ": ";
        if (full) {
            print_sig(sig);
        } else {
            cout << "(" << sig.size() << ")" << endl;
        }
        i++;
    }
}

map<string, map<string, int>> taskindex;
map<string, map<string, int>> methodindex;
map<string, map<string, int>> methodatindex;
map<string, vector<method>> task_methods;
map<string, set<string>> preceding_tasks;

map<string, vector<string>> adj_matrix;
map<string, int> discovery_time, low_link, component;
set<string> loops;
vector<string> unassigned;
int dfs_time = 0, current_component = 0;

void scc(string & task) {
    unassigned.push_back(task);
    discovery_time[task] = dfs_time;
    low_link[task] = dfs_time;
    dfs_time++;
    for (auto t : adj_matrix[task]) {
        if (task == t) {
            loops.insert(task);
        }
        if (!discovery_time.count(t)) {
            scc(t);
            low_link[task] = min(low_link[task], low_link[t]);
        } else if (!component.count(t)) {
            low_link[task] = min(low_link[task], discovery_time[t]);
        }
    }

    if (low_link[task] == discovery_time[task]) {
        bool non_trivial = false;
        if (unassigned[unassigned.size()-1] != task) {
            non_trivial = true;
        }
        while (true) {
            auto t = unassigned[unassigned.size()-1];
            unassigned.pop_back();
            component[t] = current_component;
            if (non_trivial)
                loops.insert(t);
            if (t == task)
                break;
        }
        current_component++;
    }
}

void precomputations() {
    for (auto t : primitive_tasks) {
        for (size_t i = 0; i < t.vars.size(); i++) {
            taskindex[t.name][t.vars[i].first] = i;
        }
    }
    for (auto t : abstract_tasks) {
        for (size_t i = 0; i < t.vars.size(); i++) {
            taskindex[t.name][t.vars[i].first] = i;
        }
    }
    for (auto m : methods) {
        task_methods[m.at].push_back(m);

        for (size_t i = 0; i < m.vars.size(); i++) {
            methodindex[m.name][m.vars[i].first] = i;
            methodatindex[m.name][m.vars[i].first] = -1;
        }
        for (size_t i = 0; i < m.atargs.size(); i++) {
            methodatindex[m.name][m.atargs[i]] = i;
        }

        for (auto ps : m.ps) {
            bool abort = false;
            for (auto ps2 : m.ps) {
                if (m.is_smaller(ps2, ps)) {
                    abort = true;
                    break;
                }
            }
            if (abort)
                continue;
            preceding_tasks[m.name].insert(ps.task);
        }
    }

    for (auto t : abstract_tasks) {
        for (auto m : task_methods[t.name]) {
            for (auto ps : m.ps) {
                adj_matrix[t.name].push_back(ps.task);
            }
        }
    }

    for (auto t : abstract_tasks) {
        if (!discovery_time.count(t.name)) {
            scc(t.name);
        }
    }
}

void simplefy(inf_t & A) {
    set<sig_t> set_A;
    for (auto sig_A : A)
        set_A.insert(sig_A);
    A.clear();
    for (auto sig_A : set_A)
        A.push_back(sig_A);
}

// get signature from a predicate
sig_t to_sig(vector<string> & vars) {
    sig_t sig;
    for (size_t i = 0; i < vars.size(); i++) {
        sig.push_back(vars[i]);
    }
    return sig;
}

// from subtask to method
inf_t reassign(method & m, plan_step & p, inf_t & A, bool drop_locals, bool rename) {
    if (A == ALL)
        return ALL;

    inf_t inf;
    for (auto sig_A : A) {
        bool abort = false;
        sig_t sig;
        for (auto arg_A : sig_A) {
            if (arg_A.find("__LOCAL__") == 0) {
                sig.push_back(arg_A);
                continue;
            }
            auto taskidx = taskindex[p.task][arg_A];
            auto methodidx = methodindex[m.name][p.args[taskidx]];
            auto methodatidx = methodatindex[m.name][p.args[taskidx]];
            arg_t arg;
            if (methodatidx == -1) {
                if (drop_locals) {
                    abort = true;
                    break;
                }
                if (rename)
                    arg = "__LOCAL__" + m.name + "__LOCALEND" + m.vars[methodidx].first;
                else
                    arg = m.vars[methodidx].first;
            } else {
                arg = m.atargs[methodatidx];
            }
            sig.push_back(arg);
        }
        if (abort)
            continue;
        inf.push_back(sig);
    }
    simplefy(inf);
    return inf;
}

// from method to task
inf_t reassign(task & t, method & m, inf_t & A) {
    if (A == ALL)
        return ALL;

    inf_t inf;
    for (auto sigA : A) {
        sig_t sig;
        for (auto argA : sigA) {
            if (argA.find("__LOCAL__") == 0) {
                sig.push_back(argA);
                continue;
            }
            auto methodatidx = methodatindex[m.name][argA];
            auto tasksort = sorts[t.vars[methodatidx].second];
            sig.push_back(t.vars[methodatidx].first);
        }
        inf.push_back(sig);
    }
    simplefy(inf);
    return inf;
}

void unify(inf_t & A, inf_t & B) {
    if (A == ALL || B == ALL) {
        A = ALL;
        return;
    }

    for (auto sig_B : B)
        A.push_back(sig_B);
    simplefy(A);
}

// ALL does not appear in the intersect code part, which is why it left out.
void intersect(inf_t & A, inf_t & B) {
    inf_t inf;
    for (auto sig_A : A) {
        bool abort = true;
        for (auto sig_B : B) {
            if (sig_A == sig_B) {
                abort = false;
                break;
            }
        }
        if (abort)
            continue;
        inf.push_back(sig_A);
    }
    A = inf;
}

void substract(inf_t & A, inf_t & B) {
    if (A == ALL) {
        return;
    }

    inf_t inf;
    for (auto sig_A : A) {
        bool abort = false;
        for (auto sig_B : B) {
            if (sig_A == sig_B) {
                abort = true;
                break;
            }
        }
        if (abort)
            continue;
        inf.push_back(sig_A);
    }
    A = inf;
}

void constrain(inf_t & A, inf_t & B, method & m) {
    if (B == ALL || (B.size() > 0 && B[0].size() == 0)) {
        A = {};
        return;
    }

    inf_t inf;
    for (auto sig_A : A) {
        bool abort = false;
        for (auto sig_B : B) {
            bool match = true;
            for (size_t i = 0; i < sig_A.size(); i++) {
                bool disjoint = true;
                auto sort_A = sorts[m.vars[methodindex[m.name][sig_A[i]]].second];
                auto arg_B = sig_B[i];
                string local = "LOCALEND";
                if (arg_B.find("__LOCAL__") == 0) {
                    arg_B = arg_B.substr(arg_B.find(local) + local.length());
                }
                auto sort_B = sorts[m.vars[methodindex[m.name][arg_B]].second];
                for (auto instance : sort_B) {
                    if (sort_A.count(instance)) {
                        disjoint = false;
                        break;
                    }
                }
                if (disjoint) {
                    match = false;
                    break;
                }
            }
            if (match) {
                abort = true;
                break;
            }
        }
        if (abort)
            continue;
        inf.push_back(sig_A);
    }
    A = inf;
}

vector<method> new_methods;
vector<task> new_primitive_tasks;
vector<task> new_abstract_tasks;
map<string, task> new_task_name_map;
map<string, array<size_t, 3>> prec_index;

// Adds the inferred preconditions to the domain.
void add_prec(method & m, inf_t & inf, string & predicate, bool positive) {
    size_t i;
    for (i = 0; i < methods.size(); i++) {
        if (methods[i].name == m.name) {
            break;
        }
    }
     
    for (auto sig : inf) {
        // Check if literals is already contained in all the preceding tasks (this helps against trivial inference)
        bool redundant = true;
        for (auto task : preceding_tasks[m.name]) {
            auto t = task_name_map[task];
            bool contained = false;
            for (auto prec : t.prec) {
                if (prec.positive == positive && prec.predicate == predicate && prec.arguments == sig) {
                    contained = true;
                    break;
                }
            }
            if (!contained) {
                redundant = false;
                break;
            }
        }

        // Check if literal is already contained in the inferred preconditions.
        if (!redundant && prec_index.count(m.name)) {
            auto [index, index2, index3] = prec_index[m.name];
            for (auto prec : new_primitive_tasks[index].prec) {
                if (prec.positive == positive && prec.predicate == predicate && prec.arguments == sig) {
                    redundant = true;
                    break;
                }
            }
        }

#ifndef NDEBUG
        cout << "-+"[positive] << predicate << ": ";
        print_sig(sig);
        if (redundant)
            cout << "redundant ";
        cout << "in " << m.name << endl << endl;
#endif

        if (redundant) {
            method_inferences[m.name].second++;
            continue;
        }
        method_inferences[m.name].first++;


        if (!prec_index.count(m.name)) {
            // If the method already contained a precondition action, use it instead of creating a new one.
            for (size_t j = 0; j < m.ps.size(); j++) {
                if (m.ps[j].task.find("__method_precondition_") == 0) {
                    for (size_t k = 0; k < primitive_tasks.size(); k++) {
                        if (primitive_tasks[k].name == m.ps[j].task) {
                            prec_index[m.name] = {k, j, i};
                            break;
                        }
                    }
                    break;
                }
            }
            if (!prec_index.count(m.name)) {
                plan_step ps;
                ps.id = "mprec_inference_" + m.name;
                ps.task = "__method_precondition_inference_" + m.name;

                for (auto ps2 : m.ps) {
                    m.ordering.push_back({ps.id, ps2.id});
                }
                m.ps.push_back(ps);
                new_methods[i] = m;

                task sub;
                sub.name = ps.task;
                sub.artificial = true;
                sub.number_of_original_vars = 0;

                new_primitive_tasks.push_back(sub);
                new_task_name_map[sub.name] = sub;
                prec_index[m.name] = {new_primitive_tasks.size()-1, m.ps.size()-1, i};
            }
        }

        // Generate new precondition and store in the method precondition action.
        literal l;
        l.positive = positive;
        l.isConstantCostExpression = false;
        l.isCostChangeExpression = false;
        l.predicate = predicate;
        for (auto arg : sig) {
            l.arguments.push_back(arg);
        }
        l.costValue = 0;

        auto [index, index2, index3] = prec_index[m.name];
        auto pt = new_primitive_tasks[index];
        for (auto var : l.arguments) {
            bool abort = false;
            for (auto [var2, sort] : pt.vars) {
                if (var == var2) {
                    abort = true;
                    break;
                }
            }
            if (abort)
                continue;
            new_methods[index3].ps[index2].args.push_back(var);
            pt.vars.push_back({var, m.vars[methodindex[m.name][var]].second});
        }
        pt.prec.push_back(l);
        new_primitive_tasks[index] = pt;
        new_task_name_map[pt.name] = pt;
    }
}

// DFS for calculaing the inductive empty-refinability and add-reachability
void reachable(task & t, string & predicate, bool positive) {
    if (task_data[t.name].finished)
        return;

    task_data[t.name].finished = true;

    if (loops.count(t.name)) {
        task_data[t.name].init = true;
        task_data[t.name].non_empty = {};
        task_data[t.name].add_non_empty = {};
        task_data[t.name].add_reachable = ALL;
    }

    for (auto m : task_methods[t.name]) {
        // non-emptniess
        inf_t method_non_empty, method_local_non_empty, method_add_non_empty;
        for (auto ps : m.ps) {
            reachable(task_name_map[ps.task], predicate, positive);

            auto inf_ps = reassign(m, ps, task_data[ps.task].non_empty, true, true);
            auto inf_ps_local = reassign(m, ps, task_data[ps.task].non_empty, false, false);
            unify(method_non_empty, inf_ps);
            unify(method_local_non_empty, inf_ps_local);

            inf_ps = reassign(m, ps, task_data[ps.task].add_non_empty, true, true);
            unify(method_add_non_empty, inf_ps);
        }
        auto task_non_empty = reassign(t, m, method_non_empty);
        auto task_add_non_empty = reassign(t, m, method_add_non_empty);
        if (task_data[t.name].init) {
            intersect(task_data[t.name].non_empty, task_non_empty);
            intersect(task_data[t.name].add_non_empty, task_add_non_empty);
        } else {
            task_data[t.name].init = true;
            task_data[t.name].non_empty = task_non_empty;
            task_data[t.name].add_non_empty = task_add_non_empty;
        }

        // add-reachability
        inf_t method_add_reachable;
        for (auto ps : m.ps) {
            auto inf_ps = reassign(m, ps, task_data[ps.task].add_reachable, false, true);
            for (auto ps2 : m.ps) {
                if (m.is_smaller(ps2, ps)) {
                    auto inf_ps2 = reassign(m, ps2, task_data[ps2.task].add_non_empty, false, true);
                    substract(inf_ps, inf_ps2);
                }
            }
            unify(method_add_reachable, inf_ps);
        }
        auto task_add_reachable = reassign(t, m, method_add_reachable);
        unify(task_data[t.name].add_reachable, task_add_reachable);

        // Method inferences
        auto inferred = method_local_non_empty;
        constrain(inferred, method_add_reachable, m);
        add_prec(m, inferred, predicate, positive);

#ifndef NDEBUG
        // Methods
        if (method_local_non_empty.size() == 0 && method_add_reachable.size() == 0)
            continue;
        bool verb = true;
        cout << predicate << ", " << m.name << endl;
        cout << "NE:" << endl;
        print_inf(method_local_non_empty, verb);
        cout << "AR:" << endl;
        print_inf(method_add_reachable, verb);
        cout << endl;
#endif
    }
}

void __infer_preconditions(bool positive) {
    for (auto def : predicate_definitions) {
        auto predicate = def.name;
        task_data.clear();

        // base case for non-emptiness and add-reachability
        for (auto pt : primitive_tasks) {
            task_data[pt.name].init = true;
            task_data[pt.name].finished = true;

            for (auto l : pt.eff) {
                if (l.positive == positive && l.predicate == predicate) {
                    auto sig = to_sig(l.arguments);
                    task_data[pt.name].add_reachable.push_back(sig);
                }
            }
            inf_t non_add_reachable;
            for (auto l : pt.prec) {
                if (l.positive == positive && l.predicate == predicate) {
                    auto sig = to_sig(l.arguments);
                    non_add_reachable.push_back(sig);
                }
            }
            substract(task_data[pt.name].add_reachable, non_add_reachable);

            for (auto l : pt.eff) {
                if (l.positive == positive && l.predicate == predicate) {
                    auto sig = to_sig(l.arguments);
                    task_data[pt.name].add_non_empty.push_back(sig);
                }
            }
            for (auto l : pt.prec) {
                if (l.positive == positive && l.predicate == predicate) {
                    auto sig = to_sig(l.arguments);
                    task_data[pt.name].non_empty.push_back(sig);
                    task_data[pt.name].add_non_empty.push_back(sig);
                }
            }
        }

        // inductive case for non-emptiness and add-reachability
        reachable(task_name_map["__top"], predicate, positive);
    }
}

void infer_preconditions() {
    new_methods = methods;
    new_primitive_tasks = primitive_tasks;
    new_abstract_tasks = abstract_tasks;
    new_task_name_map = task_name_map;

    precomputations();
    __infer_preconditions(true);
    __infer_preconditions(false);

    print_statistics();

    methods = new_methods;
    primitive_tasks = new_primitive_tasks;
    abstract_tasks = new_abstract_tasks;
    task_name_map = new_task_name_map;
}
