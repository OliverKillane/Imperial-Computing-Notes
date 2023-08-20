#include "table.h"

#include "joins/nested_loop.h"
#include "joins/sort_merge.h"
#include "joins/unique_sort_merge.h"
#include "joins/hash.h"
#include "joins/unique_hash.h"

#include <iostream>

using namespace std;

void example_equality() {
    Table<int, bool> t {
        .name = "t",
        .cols = {"x", "?"},
        .rows = {
            {2,true},
            {3,false},
            {1,true},
        }
    };
    cout << t;
    t.sort_rows();
    cout << t;
}

void example_basic() {
    Table<string, int> tab {
        .name = "galactic_bar_tab",
        .cols = {"name", "credits"},
        .rows = {
            {"anakin skywalker",   102},
            {"luke skywalker",       4},
            {"han solo",           300},
            {"yoda",            120024},
        }
    };
    cout << tab;


    Table<string, int> ages {
        .name = "character_ages",
        .cols = {"name", "age"},
        .rows = {
            {"darth vader",    45},
            {"luke skywalker", 53},
            {"han solo",       66},
            {"yoda",          900},
        }
    };
    cout << ages;

    auto joined = hash_join<0, 0>(tab, ages);
    cout << joined;
}

void example_sort_merges() {
    Table<int, string> repeat {
        .name = "reps",
        .cols = {"id", "n"},
        .rows = {
            {1, "first" },
            {2, "second"},
            {2, "third" },
            {3, "fourth"},
        }
    };
    cout << repeat;
    
    auto unique_joined = unique_sort_merge_join<0,0>(repeat, repeat);
    auto joined = sort_merge_join<0,0>(repeat, repeat);

    // here we demonstrate that the simple sort merge (unique) only works when 
    // the attributes joined on are unique in each table

    cout << "unique sort merge (incorrect result)" << endl << unique_joined;
    cout << "normal sort merge (correct result)" << endl << joined;
}

void example_three_way_join() {
    Table<int64_t, int64_t> ab{
        .name = "ab",
        .cols = {"a", "b"},
        .rows = {
            {1,2},
        }
    };
    cout << ab;

    Table<int64_t, int64_t> cd{
        .name = "cd",
        .cols = {"c", "d"},
        .rows = {
            {2,3},
        }
    };
    cout << cd;

    Table<int64_t, int64_t> ef{
        .name = "ef",
        .cols = {"e", "f"},
        .rows = {
            {3,4},
        }
    };
    cout << ef;

    auto cdef = hash_join<1,0>(cd, ef);
    cout << cdef;
    auto abcdef = sort_merge_join<1,0>(ab, cdef);

    cout << abcdef;
}

int main() {
    example_equality();
    example_basic();
    example_sort_merges();
    example_three_way_join();
}
