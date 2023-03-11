#include <iostream>
#include <vector>
#include <mutex>
#include <memory>
#include <atomic>
#include <functional>
#include <stdexcept>

using namespace std;
/* UNFINISHED */

class AbortTransaction : public std::exception {
public:
    char * what () override {return "Transaction Aborted";}
};

using TimeStamp = chrono::time_point<std::chrono::system_clock>;

template<typename Row>
class Transaction;

/* A Table abstraction, using rows of type Row 
 * (e.g `vector<variant<int, int>>`, or for simpler testing `int`) 
 */
template<typename Row>
class Table {
    /* Overriden to provide << stream implementation */
    virtual ostream& printInternals(ostream &os) = 0;

    friend ostream& operator<<(ostream &os, const Table<Row> &table) {
        return table.printInternals(os);
    }
public:
    /* The table name  */
    const string name;

    /* transaction operations (accessible by transaction)
     * - Throw AbortTransaction exception to abort a transaction
     * - Write to the transaction log with t.log("something happened")
     */
    virtual void write(Transaction<Row>& t, size_t index, Row&& data) = 0;
    virtual Row  read(Transaction<Row>& t, size_t index) = 0;
    virtual void append(Transaction<Row>& t, Row&& data) = 0;
};

template<typename Row>
using TableGroup = unordered_map<string, Table<Row>>;

template<typename Row>
class Transaction {
    using TransFn = std::function<bool(Transaction<Row>&, TableGroup<Row>&)>;

    // For unique IDs
    static atomic<size_t> current_id_;

    vector<string> log_; // Recorded actions by all tables
    const TransFn function_;         // The transaction function to apply
    const size_t id_;                // The transaction's ID
    const TableGroup<Row>& tables_;  // Tables the trasaction can access

public:
    Transaction(TransFn function, TableGroup<Row>& tables) : 
        function_(function), 
        id_(current_id_++), 
        tables_(tables) {}

    void log(string&& msg) {
        log.emplace_back(msg);
    }

    void run() {
        try {
            function_(, tables_);
            cout << "Committed transaction T" << id_;
        } catch (AbortTransaction abort) {
            cout << "Aborted transaction T" << id_ << ":" << endl << abort.what() << endl;
        }
    }
};


template<typename Row>
class TimeStampOrderTable : public Table<Row> {
    struct TimeStampedRow {
        Row data;
        TimeStamp read;
        TimeStamp write;
    };

    vector<TimeStampedRow> rows_;
    mutex internal_m_;

    void printInternals(ostream &os) override {
        auto printtime = [&](TimeStamp ts) {
            const time_t ts_local = chrono::system_clock::to_time_t(ts);
            os << put_time(localtime(&ts_local), "%F %T");
        };

        const lock_guard<mutex> lock(internal_m_);
        os << "Table " name << ":" << endl;
        for (size_t index = 0; index < rows_.size(); rows++) {
            os << index << ": " << "R[";
            printtime(rows_[index].read);
            os << "] W[";
            printtime(rows_[index].write);   
            os << "] " << rows_[index].data;
        }
        return os;
    }


public:
    void write(Transaction& ts, size_t index, Row&& data) override {
        const lock_guard<mutex> lock(internal_m_);
        TimeStampedRow& row = rows_[index]; // throws on index out of range

        if (row.write > ts) {
            return false;
        } else {
            row.data = data;
            return true;
        }
    }

    optional<Row> read(TimeStamp ts, size_t index) override {
        const lock_guard<mutex> lock(internal_m_);
        TimeStampedRow& row = rows_[index]; // throws on index out of range

        if (row.read > ts) {
            return {};
        } else {
            return row.data;
        }
    }

    void append(TimeStamp ts, Row&& data) override {
        const lock_guard<mutex> lock(internal_m_);
        rows_.emplace_back({.read = ts, .write = ts, .data = data});
    }
};




int main() {
    TableGroup<int> tables();
    tables["table 1"] = TimeStampOrderTable<int>();
    tables["table 2"] = TimeStampOrderTable<int>();

    Transaction<int> T1([](ts, tgp){
        tgp["table 1"].append(ts, 20);
        tgp["table 1"].append(ts, 21);
        tgp["table 1"].append(ts, 22);

        tgp["table 1"].write(ts, 1, 13) &&
        tgp["table 1"].write(ts, 1, 13);
    });

    T1.run();
    T2.run();
}

