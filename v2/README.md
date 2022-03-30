# Attempting to recapture the specification of Paul Rowe's paper titled "Confining Adversary Actions via Measurements"

My version is created in tandam with Dr. Alexander's previous work as well as our current thoughts. 

To run the theories, simply clone the respository. From the `v2` folder type `make`. Then you can open and run the .v files in you editor of choice. 

## Notes Mar 29 2022
After a meeting with Perry this morning, we have come to conclude that the poset of events is a strict partial order. Not simply a partial order. In this way, the properties of the order are antireflexive, asymmetric, and transitive. This makes sense as these are all the properties we want. 

We also decided that the poset of events may be a semi lattice. More to come on that. 

## Notes Mar 9 2022
What is meant by "adversary ordered"? From the paper, we conclude that if a set of events `E` is adversary ordered then it is ordered.

Today I also worked more on the `confining` spec. I added an example realation and tried to prove it is transitive. I couldn't get the proof to work. I'm guess becuase using the Coq predefined `transitive` is too general. I think I must specifiy the exact transitive relation instead of using a forall. 


## Notes Mar 8 2022
Perry and I discussed adding a module system to hold all axioms and parameters in the confining paper to generalize about specifications for future systems. So, I started thinking about this idea and created the file `module.v` Upon working in this file, I realized I need to better understand the system in the `confining` paper before abstracting it. I plan to keep going on the `confining` specification in the coming days. 
