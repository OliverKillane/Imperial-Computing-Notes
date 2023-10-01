class WindowSumAggregator : public PushOperator<float> {
  PushOperator<float> *plan_;

  // a circular buffer window
  // the next index after buffer_i_ is the start of the window
  std::vector<float> window_buffer_;

  size_t buffer_i_ = 0;
  float aggregate = 0;

  // for checking the window is filled
  size_t count_ = 0;

public:
  WindowSumAggregator(PushOperator<float> *plan, size_t windowsize)
      : plan_(plan), window_buffer_(windowsize) {}

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