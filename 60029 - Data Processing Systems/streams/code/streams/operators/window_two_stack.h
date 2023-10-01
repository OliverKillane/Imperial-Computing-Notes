
// To improve: we can use one vector instead of two separate
template <typename Event, Event agg(Event &, Event &)>
class WindowTwoStackAggregator : public PushOperator<Event> {
  PushOperator<Event> *plan_;

  // front stack
  std::vector<Event> front_values_;
  std::vector<Event> front_agg_;

  // back stack
  std::vector<Event> back_values_;
  std::vector<Event> back_agg_;

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
  void push_front(Event r) {
    if (window_pos == 0) {
      front_values_[0] = r;
      front_agg_[0] = r;
    } else {
      front_values_[window_pos] = r;
      front_agg_[window_pos] = agg(r, front_agg_[window_pos - 1]);
    }
  }

public:
  WindowTwoStackAggregator(PushOperator<Event> *plan, size_t window_size)
      : plan_(plan), front_values_(window_size), front_agg_(window_size),
        back_values_(window_size), back_agg_(window_size) {}

  void process(Event r) override {
    size_t max_size = front_values_.size();

    if (count_ < max_size) {
      push_front(r);
      window_pos++;
    } else {
      if (window_pos == max_size) {
        flip();
      }

      push_front(r);
      plan_->process(
          agg(front_agg_[window_pos], back_agg_[max_size - 1 - window_pos]));
      window_pos++;
    }

    count_++;
  }
};
