## Definition
Data centre hardware and software that vendors use to offer computing resources & services.
- Pool of easily usable, virtualised resources (e.g VMs), and services (e.g [[Bigtable]], [[Dynamo]])
- Typically easily scalable (dynamically provisioned compute resources)
- Typically charged for usage (resources acquired and released on demand)

Some Providers are [[Google Cloud Platform]], [[Amazon Web Services]] and [[Microsoft Azure]].

| Cloud Type | Description |
|-|-|
| Public | All hardware and software, and supporting infrastructure is owned by the provider (e.g [[Google Cloud Platform]], [[Amazon Web Services]] and [[Microsoft Azure]].) Resources offered over the internet.|
| Private | Infrastructure is hosted by the company using it, all on-site on a private network. |
| Hybrid | Data and applications shared between a private and public cloud setup. |
### Benefits
- *Speed* - can provision new resources & services immediately, rather than waiting to order and set up own hardware
- *Elasticity* - Only paying for usage, if demand is varied then compute can be scaled automatically, and the company only pays for usage. 
- *Global Scale* - Can be available worldwide, easily provision compute in different regions
- *Security* - The provider is responsible for much of the security, and provides their own services to help with this.
- *Economies of Scale* - Large datacentres have a lower cost per unit, providers can justify cost of micro-optimising their own hardware, software with huge scale.  
### Costs
- Dependency of connection to the cloud provider (rather than using machines onsite for a purpose onsite), though this does not apply to consumer facing applications.
- *Vendor lock-in* - if too dependent on a single vendor, a company needs to price-in the risk of increased fees.
## Cloud Service Models
$$\underbrace{IaaS \to PaaS \to Faas \to SaaS}_{\text{less } \to \text{ more control}}$$
### Infrastructure-as-a-Service (IaaS)
$$\underbrace{\text{App Data Runtime Middleware OS}}_{\text{Customer}} \ \underbrace{\text{Virtualization Servers Storage Networking}}_{\text{Provider}}$$
Provider leases servers & VMs, as well as storage, network, security infrastructure.
- Customers write their own software, manage deployment to their leased machines
- Provider pools resources to share serve multiple customers
### Platform-as-a-Service
$$\underbrace{\text{App Data}}_{\text{Customer}} \ \underbrace{\text{Runtime Middleware OS Virtualization Servers Storage Networking}}_{\text{Provider}}$$
On-demand environment for development, testing and management provided.
- servers, storage, network, OS etc
- The current most popular model
### Function-as-a-Service
Customer builds serverless functionality (e.g AWS Lambdas), deploys. Provider manages servers and infrastructure.
- Customer only concerned with code, no exposure to what VMs, network etc is set up.
### Software-as-a-Service
$$\underbrace{\text{App Data Runtime Middleware OS Virtualization Servers Storage Networking}}_{\text{Provider}}$$
Provider provides applications over the internet on demand.
- All underlying app dev/infrastructure/setup is managed by the vendor
- All maintenance completed by vendor.
For example a company may use slack, office365.