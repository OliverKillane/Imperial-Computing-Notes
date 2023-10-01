template <typename Event> class Output : public PushOperator<Event> {
  std::ostream &output_;

public:
  Output(std::ostream &output) : output_(output) {}

  void process(Event data) override { output_ << "->" << data << std::endl; }
};