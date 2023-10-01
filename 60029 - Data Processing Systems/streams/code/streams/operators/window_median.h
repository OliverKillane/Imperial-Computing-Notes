class WindowMedianAggregator : public PushOperator<float> {
  PushOperator<float> *plan_;
  std::vector<float> window_buffer_;
  size_t buffer_i_ = 0;

  // for checking the window is filled
  size_t count_ = 0;

public:
  WindowMedianAggregator(PushOperator<float> *plan, size_t window_size)
      : plan_(plan), window_buffer_(window_size) {}

  void process(float f) override {
    const size_t size = window_buffer_.size();
    buffer_i_ = (buffer_i_ + 1) % size;
    window_buffer_[buffer_i_] = f;
    count_++;
    if (count_ > size) {

      // copy and sort, this can be made much more efficient using a multiset
      // and vector see multiset median trick:
      // https://codeforces.com/blog/entry/68300
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