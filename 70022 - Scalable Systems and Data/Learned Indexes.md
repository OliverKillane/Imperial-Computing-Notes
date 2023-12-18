## Definition
Using a model based on current data to estimate the position of data in a table. It is an index, with some known bound on error.
- Often a continuous function, can include neural-networks, regression, [[Piecewise Linear Function]]. 
- Used as a type of [[Main Memory Indexing]]
### Issues with Traditional ML
- Models are large, inference is slower than existing indexes (e.g. [[B+ Tree]]).
- Overfitting is avoided, but in [[Learned Indexes]] overfitting is beneficial.
### Tradition Index Advantages
- guarantee on lookup time
- update time guarantee
- can handle all data types & data distributions
- well-studied, available on many data processing systems, and some with hardware support
### Learned Index Advantages
- Considers the pattern of available data
- Lookup time guarantee on read-only data (distribution does not change, error does not change)
### Learned Index Disadvantages
- Updates are difficult (distribution changes, error bound changes)
- Retraining for updates is slow
- Not all key types work 
- Not yet applied to multidimensional data

### Corrective Models
If a prediction has large error for key $k$, then it probably has similar error for nearly keys such as $(k + 1)$
- we can record the error from lookup on a few reference keys, store it, and then use it to correct our predictions. 
## Model Assisted Index
For example the MAB+ tree (Model Assisted [[B+ Tree]]) 
- uses a *CDF model* to predict the location of a first result $key \mapsto \widehat{pos}(key)$
- *Corrective Model* used to eliminate local bias from prediction, $\widehat{pos} \mapsto \widehat{pos}'$
- Larger nodes used (can better predict location within a node), the model and correction metadata is embedded in each node along side the values, and pointers.