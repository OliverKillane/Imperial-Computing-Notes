template<typename Event>
class PushOperator {
public:
    // return pressure on operator
    virtual float process(Event data) = 0;
};