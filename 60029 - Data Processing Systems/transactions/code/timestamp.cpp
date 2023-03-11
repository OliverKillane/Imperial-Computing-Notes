#include <iostream>
#include <map>
#include <tuple>
#include <atomic>
#include <chrono>
#include <mutex>
#include <iomanip>

using namespace std;
/* UNFINISHED */

// for example with a basic in-memory n-ary table
template<typename RowData>
class Table {
    using TimeStamp = chrono::time_point<std::chrono::system_clock>;

    struct Row {
        Row(TimeStamp trans_ts, RowData&& data) : 
            read(trans_ts), 
            write(trans_ts), data(data) {}
        
        TimeStamp read;
        TimeStamp write;
        RowData data;
        mutex row_mutex;
    };
    
    string name;
    map<size_t, Row> rows;

    friend ostream &operator<<(std::ostream &os, const Table<RowData> &table) {
        auto printtime = [&](TimeStamp ts) {
            const time_t ts_local = chrono::system_clock::to_time_t(ts);
            os << put_time(localtime(&ts_local), "%F %T") << flush;
        };
        
        os << table.name << ": " << endl;
        for (auto& elem : table.rows) {
            os << elem.first << ": ";
            const auto& row = elem.second;
            os << "R[";
            printtime(row.read);
            os << "] W[";
            printtime(row.write);
            os << "] data: " << row.data << endl;
        }
        return os;
    }

public:

    Table(string&& name) : name(name) {}

    // return true on success, if false => abort transaction
    bool writeRow(RowData&& data, size_t index, TimeStamp trans_ts) {
        Row& row = rows[index]; // reference to the index, not the row struct
        const lock_guard<mutex> lock(row.row_mutex);

        if (row.write > trans_ts) {
            return false;
        }
        
        row.data = data;
        row.write = trans_ts;
        return true;
    }

    // return data on success, if empty => abort transaction
    optional<RowData> readRow(size_t index, TimeStamp trans_ts) {
        if (rows.contains)
        rows.at(index, Row(trans_ts, ); // reference to the index, not the row struct
        const lock_guard<mutex> lock(row.row_mutex);

        if (row.read > trans_ts) {
            return {};
        }
        row.read = trans_ts;
        return row.data;
    }
};



int main() {
    Table<int> a("Test");
    auto trans_ts = chrono::system_clock::now();

    a.writeRow(3, 0, trans_ts);
    a.writeRow(3, 1, trans_ts);
    a.writeRow(3, 3, trans_ts);
    a.writeRow(101, 101, trans_ts);
    auto trans_ts_2 = chrono::system_clock::now();
    a.readRow(101, trans_ts_2);
    cout << a << endl;

}