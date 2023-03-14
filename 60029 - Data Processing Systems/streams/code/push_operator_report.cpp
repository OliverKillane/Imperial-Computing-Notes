

template<typename Row>
class PushOperator {
public:
    virtual float process(Row data) = 0;
};