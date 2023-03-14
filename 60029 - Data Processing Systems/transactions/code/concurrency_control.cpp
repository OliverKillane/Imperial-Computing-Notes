#include <iostream>
#include <vector>
#include <mutex>
#include <memory>
#include <atomic>
#include <functional>
#include <stdexcept>
#include <iomanip>
#include <functional>

using namespace std;

// Exception for aborting transactions
class AbortTransaction : public std::exception {
public:
    const char* what() const noexcept override {return "Transaction Aborted";}
};

// Exception for getting transaction data (not yet run)
class TransactionNotStarted : public std::exception {
public:
    const char* what() const noexcept override {return "Transaction Not Yet Started";}
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

    Table(string&& name) : name(name) {}

    /* transaction operations (accessible by transaction)
     * - Throw AbortTransaction exception to abort a transaction
     * - Write to the transaction log with t.log("something happened")
     */
    virtual void write(Transaction<Table<Row>>& t, size_t index, Row&& data) = 0;
    virtual Row  read(Transaction<Table<Row>>& t, size_t index) const = 0;
    virtual void append(Transaction<Table<Row>>& t, Row&& data) = 0;
};


// Group of tables
// - Not thread-safe
template <typename TableType>
class TableManager {
    unordered_map<string, reference_wrapper<TableType>> tables_;
public:
    // insert a new table, override a table with the same name.
    void insertTable(TableType& table) {
        tables_.insert_or_assign(table.name, table);
    }

    TableType& getTable(string&& tablename) {
        return tables_.at(tablename);
    }
};


template<typename TableType>
class Transaction {
    using TransFn = std::function<bool(Transaction<TableType>&, TableManager<TableType>&)>;

    // For unique IDs
    static atomic<size_t> current_id_;

    vector<string> log_;             // Recorded actions by all tables
    const TransFn function_;         // The transaction function to apply
    const size_t id_;                // The transaction's ID
    const TableManager<TableType>& tables_;  // Tables the transaction can access
    optional<TimeStamp> start_ts_;

    friend ostream& operator<<(ostream &os, const Transaction<TableType> &trans) {
        os << "transaction T" << trans.id_ << endl << "Log: " << endl;
        for (size_t i = 0; i < trans.log_.size(); i++) {
            os << "\t" << i << ": " << trans.log_[i];
        }
        return os;
    }

public:
    Transaction(TransFn function, TableManager<TableType>& tables) : 
        function_(function), 
        id_(current_id_++), 
        tables_(tables), start_ts_() {}

    void log(string&& msg) {
        log_.emplace_back(msg);
    }

    TimeStamp getStart() const {
        if (start_ts_.has_value()) {
            return start_ts_.value();
        } else {
            throw TransactionNotStarted();
        }
    }

    void run() {
        try {
            start_ts_ = chrono::system_clock::now();
            function_(*this, tables_);
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
        mutable TimeStamp read;
        mutable TimeStamp write;
    };

    vector<TimeStampedRow> rows_;
    mutable mutex internal_m_;

    ostream& printInternals(ostream& os) override {
        auto printtime = [&](TimeStamp ts) {
            const time_t ts_local = chrono::system_clock::to_time_t(ts);
            os << put_time(localtime(&ts_local), "%F %T");
        };

        const lock_guard<mutex> lock(internal_m_);
        os << "Table " << Table<Row>::name << ":" << endl;
        for (size_t index = 0; index < rows_.size(); index++) {
            os << index << ": " << "R[";
            printtime(rows_[index].read);
            os << "] W[";
            printtime(rows_[index].write);   
            os << "] " << rows_[index].data;
        }
        return os;
    }

public:
    TimeStampOrderTable(string&& name) : Table<Row>(move(name)) {}

    void write(Transaction<Row>& t, size_t index, Row&& data) override {
        const lock_guard<mutex> lock(internal_m_);
        auto& row = rows_[index]; // throws on index out of range
        auto ts = t.getStart();
        if (row.write > ts) {
            throw AbortTransaction();
        } else {
            row.write = ts;
            row.data = data;
        }
    }

    Row read(Transaction<Row>& t, size_t index) const override {
        const lock_guard<mutex> lock(internal_m_);
        auto& row = rows_[index]; // throws on index out of range
        auto ts = t.getStart();

        if (row.read > ts) {
            throw AbortTransaction();
        } else {
            row.read = ts;
            return row.data;
        }
    }

    void append(Transaction<Row>& t, Row&& data) override {
        const lock_guard<mutex> lock(internal_m_);
        auto ts = t.getStart();
        rows_.emplace_back(TimeStampedRow {.data = data, .read = ts, .write = ts});
    }
};




int main() {
    using TableType = TimeStampOrderTable<int>;

    TableType table1("table1");
    TableType table2("table2");

    TableManager<TableType> tables;
    tables.insertTable(table1);
    tables.insertTable(table2);


    Transaction<TableType> T1([](auto t, auto tm){
        auto& table1 = tm.getTable("table1");
        table1.append(t, 3);
        table1.append(t, 45);
        table1.append(t, 66);
        t.log("here!");
        table1.write(t, 0, 33);
    }, tables);

    // T1.run();
    // T2.run();
}

