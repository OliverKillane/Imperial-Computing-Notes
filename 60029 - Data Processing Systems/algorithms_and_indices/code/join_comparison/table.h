#pragma once
#include <tuple>
#include <vector>
#include <string>
#include <iostream>
#include <sstream>

using namespace std;

// Used for equality - need to sort tuples by all fields
template<size_t index, typename... Ts> bool tup_comp(const tuple<Ts...>& t1, const tuple<Ts...>& t2) {
    if constexpr (index < sizeof...(Ts)) {
        if (get<index>(t1) < get<index>(t2)) {
            return true;
        } else if (get<index>(t1) > get<index>(t2)) {
            return false;
        } else {
            return tup_comp<index + 1, Ts...>(t1, t2);
        }
    } else {
        return false;
    }
}


// For simplicity, we use n-ary tables, and have the types specified at compile 
// time & use indexes to access columns in our tuples.
// 
// Hence it is possible to create:
// Table<int, string, bool>
// 
// This is not representative of an *actual* system, as here we know:
// - how many columns exist
// - the types of each column
// - the location (the entirety of a table is always in memory)
// and we can let the C++ type system decide if some join is valid
template <typename... types> struct Table {
    string name;
    array<string, sizeof...(types)> cols;
    vector<tuple<types...>> rows;

    void sort_rows() {
        // used as easy way to write unordered vector comparison without maps
        // just copy and sort both!
        // - inefficient & requires < on all types,
        // - not always correct / sort stability
        sort(rows.begin(), rows.end(), tup_comp<0, types...>);
    }

    inline bool operator==(const Table<types...>& rhs) const {
        return name == rhs.name && cols == rhs.cols && rows == rhs.rows;
    }

    friend std::ostream &operator<<(std::ostream &os, const Table<types...> & t) {
        constexpr auto num_cols = sizeof...(types);
        array<vector<string>, num_cols> cols;
        array<size_t, num_cols> max_len;
        for (auto col = 0; col < num_cols; col++) {
            max_len[col] = table.cols[col].size();
        }
        append_rows<0, num_cols, types...>(table, cols, max_len);
        
        const string sep = "│";
        os << endl << " " << table.name << endl;
        os << sep;
        for (auto col = 0; col < num_cols; col++) {
            os << string(max_len[col] - table.cols[col].size(), ' ') << table.cols[col] << sep;
        }
        os << endl << sep;
        for (auto col = 0; col < num_cols; col++) {
            for (auto c  = 0; c < max_len[col]; c++) {
                os << "┄";
            }
            os << sep;
        }
        os << endl;
        for (auto row = 0; row < table.rows.size(); row++) {
            os << sep;
            for (auto col = 0; col < num_cols; col++) {
                const string val = cols[col][row];
                os << string(max_len[col] - val.size(), ' ');
                os << val << sep;
            }
            os << endl;
        }
        os << endl;
        return os;
    }
};



// Helpers for printing tables to stdout 
template<size_t col, size_t num_cols, typename... types>
void append_rows(
    const Table<types...>& table, 
    array<vector<string>, num_cols>& cols,
    array<size_t, num_cols>& max_len
    ) {
    if constexpr (col < num_cols) {
        for (const auto& row : table.rows) {
            stringstream ss;
            ss << get<col>(row);
            std::string row_str = ss.str();
            max_len[col] = max(max_len[col], row_str.size());
            cols[col].push_back(move(row_str));
        }
        append_rows<col + 1, num_cols, types...>(table, cols, max_len);
    }
}

// Helper for creating the name and columns of a new table from a join
template<size_t leftCol, size_t rightCol, typename... leftTypes, typename... rightTypes> 
Table<leftTypes..., rightTypes...> join_empty(const Table<leftTypes...>& left, const Table<rightTypes...>& right)  {
    const auto rightSize = sizeof...(rightTypes);
    const auto leftSize = sizeof...(leftTypes);
    
    array<string, leftSize + rightSize> cols;
    for (auto i = 0; i < leftSize; i++) {
        cols[i] = left.name + "." + left.cols[i];
    }
    for (auto i = 0; i < rightSize; i++) {
        cols[i + leftSize] = right.name + "." + right.cols[i];
    }
    
    return {
        .name = "(" + left.name + " JOIN " + right.name + " ON " + left.cols[leftCol] + " = " + right.cols[rightCol] + ")",
        .cols = move(cols),
        .rows = {}
    };
}
