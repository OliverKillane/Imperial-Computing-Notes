#include <vector>
#include <functional>
#include <iostream>
#include <memory>
#include <algorithm>
#include <cassert>

template<typename Row>
class PushOperator {
public:
    virtual void process(Row data) = 0;
};

template<typename Row>
class Output : public PushOperator<Row> {
    std::ostream& output_;
public:
    Output(std::ostream& output) : output_(output) {}

    void process(Row data) override {
        output_ << "->" << data << std::endl;
    }
};

template<typename Row>
class Select : public PushOperator<Row> {
    PushOperator<Row>* plan_;
    std::function<bool(Row&)> predicate_;
public:
    Select(PushOperator<Row>* plan, std::function<bool(Row&)> predicate) : plan_(plan), predicate_(predicate) {}

    void process(Row data) override {
        if (predicate_(data)) plan_->process(std::move(data));
    }
};

template<typename InputRow, typename OutputRow = InputRow>
class Project : public PushOperator<InputRow> {
    PushOperator<OutputRow>* plan_;
    std::function<OutputRow(InputRow)> function_;
public:
    Project(PushOperator<OutputRow>* plan, std::function<OutputRow(InputRow)> function) : plan_(plan), function_(function) {}

    void process(InputRow data) override {
        plan_->process(function_(std::move(data)));
    }
};

template<typename Row>
class Source {
public:
    virtual void run() = 0;
};

template<typename Row>
class UserInput : public Source<Row> {
    PushOperator<Row>* plan_;
    std::istream& src_;
public:
    UserInput(PushOperator<Row>* plan, std::istream& src) : plan_(plan), src_{src} {}

    void run() override {
        for (Row r;;src_ >> r) plan_->process(std::move(r));
    }
};

class WindowSumAggregator : public PushOperator<float> {
    PushOperator<float>* plan_;

    // a circular buffer window
    // the next index after buffer_i_ is the start of the window
    std::vector<float> window_buffer_; 

    size_t buffer_i_ = 0;
    float aggregate = 0;

    // for checking the window is filled
    size_t count_ = 0;
public:
    WindowSumAggregator(PushOperator<float>* plan, size_t windowsize) : plan_(plan), window_buffer_(windowsize) {}

    void process(float f) override {
        buffer_i_ = (buffer_i_ + 1) % window_buffer_.size();
        aggregate += f;
        count_++;
        if (count_ > window_buffer_.size()) {
            aggregate -= window_buffer_[buffer_i_];
            window_buffer_[buffer_i_] = f;
            plan_->process(aggregate);
        } else {
            window_buffer_[buffer_i_] = f;
        }
    }
};

class WindowMedianAggregator : public PushOperator<float> {
    PushOperator<float>* plan_;
    std::vector<float> window_buffer_;
    size_t buffer_i_ = 0;

    // for checking the window is filled
    size_t count_ = 0;
public:
    WindowMedianAggregator(PushOperator<float>* plan, size_t window_size) : plan_(plan), window_buffer_(window_size) {}

    void process(float f) override {
        const size_t size = window_buffer_.size();
        buffer_i_ = (buffer_i_ + 1) % size;
        window_buffer_[buffer_i_] = f;
        count_++;
        if (count_ > size) {
            
            // copy and sort, this can be made much more efficient using a multiset and vector
            // see multiset median trick: https://codeforces.com/blog/entry/68300
            std::vector<float> sorted = window_buffer_;
            std::sort(sorted.begin(), sorted.end());
            
            // if even size get average of two middle, else middle element
            if (size % 2 == 0) {
                plan_->process((sorted[size / 2] + sorted[(size / 2) - 1]) / 2);
            } else {
                plan_->process(sorted[size / 2]);
            }
        }
    }
};

template<typename Row, Row agg(Row&, Row&)>
class WindowTwoStackAggregator : public PushOperator<Row> {
    PushOperator<Row>* plan_;

    // front stack
    std::vector<Row> front_values_;
    std::vector<Row> front_agg_;

    // back stack
    std::vector<Row> back_values_;
    std::vector<Row> back_agg_;

    // track the top of front and back stacks
    size_t window_pos = 0;

    // to determine when to start outputting aggregates
    size_t count_ = 0;

    // flip front stack to back stack, sets window_pos = 0
    // invariants:
    // - Must have window_size items present
    void flip() {
        size_t size = front_values_.size();
        assert(window_pos == size);

        for (size_t i = 0; i < size; i++) {
            back_values_[size - 1 - i] = front_values_[i];
        }

        back_agg_[0] = back_values_[0];
        for (size_t i = 1; i < size; i++) {
            back_agg_[i] = agg(back_agg_[i - 1], back_values_[i]);
        }

        window_pos = 0;
    }

    // Push an item to the front_stack
    // leaves the window_pos untouched 
    void push_front(Row r) {
        if (window_pos == 0) {
            front_values_[0] = r;
            front_agg_[0] = r;
        } else {
            front_values_[window_pos] = r;
            front_agg_[window_pos] = agg(r, front_agg_[window_pos - 1]);
        }
    }

public:
    WindowTwoStackAggregator(PushOperator<Row>* plan, size_t window_size) :
        plan_(plan),
        front_values_(window_size),
        front_agg_(window_size),
        back_values_(window_size),
        back_agg_(window_size) {}

    void process(Row r) override {
        size_t max_size = front_values_.size();

        if (count_ < max_size) {
            push_front(r);
            window_pos++;
        } else {
            if (window_pos == max_size) {
                flip();
            }

            push_front(r);
            plan_->process(agg(front_agg_[window_pos], back_agg_[max_size - 1 - window_pos]));
            window_pos++;
        }

        count_++;
    }
};

void example_1() {
    Output<int> console(std::cout);
    Project<int, int> mult(&console, [](auto i){return i * 3;});
    Select<int> even(&mult, [](auto& i){return i % 2 == 0;});
    UserInput<int> user(&even, std::cin);

    user.run();
}

void example_2() {
    Output<float> console(std::cout);
    WindowSumAggregator sum(&console, 4);
    Project<int, float> mult(&sum, [](auto i){return static_cast<float>(i);});
    Select<int> even(&mult, [](auto& i){return i % 2 == 0;});
    UserInput<int> user(&even, std::cin);

    user.run();
}

int intmax(int& a, int& b) {
    return std::max(a,b);
}

void example_3() {
    Output<int> console(std::cout);
    WindowTwoStackAggregator<int, intmax> maxints(&console, 3);
    UserInput<int> user(&maxints, std::cin);

    user.run();
}

int main() {
    // example_1();
    // example_2();
    example_3();
}