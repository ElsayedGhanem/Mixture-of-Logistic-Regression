rm(list=ls())
n0 <- c(25,100)
p0 <- 5   
rho0 <- c(0.9,0.95,0.99)  
phi0 <- c(0.8,0.9,0.9)  
rho0t <- rho0[1]
phi0t <- phi0[1]
n0t <- n0[1]
n0test <- 50
M0 <- 2 
pi0 <- c(0.7,0.3)
Beta01 <-  c(1,3,4,5,6)
Beta02 <-  c(-1,-1,-2,-3,-5)
Beta0 <- rbind(Beta01,Beta02)
maxit_em0 <- 200
epsilon_em0 <-1e-5 
tol_irwls0 <- 1e-3
CN0 <- 2000          
Nsim <- 2000        
Lower0 <- -1
Upper0 <- 1
tho0 <- 0.05
la0 <- 10


Beta.01 <- Beta0-(-2)
Beta.02 <- Beta0-(+2)

pi.01 <- c(0.5,0.5)
pi.02 <- c(0.3,0.7)


Design_Matrix <- function(n,p,rho,phi)
{
  x <- matrix(NA, nrow=n, ncol=(p-1))
  wr <- rnorm(n*(p-1),mean=0,sd=1)
  wr <- matrix(wr, nrow=n, ncol=p-1)
  wf <- rnorm(n,0,1)
  for (i in 1:n) {
    for (j in 1:(p-1)) {
      if (j==1||j==2) {
        x[i,j]= (1-phi^2)*wr[i,j]+phi*wf[i]
      }
      else {
        x[i,j]= (1-rho^2)*wr[i,j]+rho*wf[i]
      }
    }
  }
  x <- cbind(1,x)
  return(x)
}


etaFun <- function(x,beta)
{
  1/ (1+exp(-x%*%beta))
}


Design_Response_Mixture <- function(x, beta,pi,M)
{
  n <- dim(x)[1]
  L <- length(pi)
  m <- sample(x=1:M, size=n, replace=TRUE, prob=pi)
  y <- rep(NA,n)
  class_Assigned=matrix(data=0, nrow=n, ncol=L)
  for(j in 1:M)
  {
    IndJ <- m==j
    nj <- sum(m==j)
    etaj <- 1/ (1+exp(-x[IndJ,]%*%beta[j,]))
    y[IndJ] <- rbinom(n=nj, size=1, prob=etaj)
    class_Assigned[IndJ,j]<-1
  }
  res<-cbind(y,class_Assigned)
    return(res)
}


Design_Tau <- function(x,y,beta,pi)
{
  n <- dim(x)[1]
  L <- length(pi)
  tau_Matrix <- matrix(data=NA, nrow=n, ncol=L)
  for (j in 1:L) 
  {
    for (i in 1:n) 
    {
      P_j <- etaFun(x[i,],beta[j,])
      tau_ij <- pi[j]*(P_j^y[i])*((1-P_j)^(1-y[i]))
      tau_Matrix[i,j] <- tau_ij
    }
  }
  dev <- rowSums(tau_Matrix)
  tau <- apply(tau_Matrix, 2, "/", dev)
  return(tau)
}


Zstoc <- function(tau)
{
  n <- dim(tau)[1]
  L <- dim(tau)[2]
  z <- matrix(data=0, nrow=n, ncol=L)
  for (i in 1:n)
  {
    z[i,] <- t(rmultinom(n=1,size=1,prob=c(tau[i,])))
  }
  return(z)
}



irwls_mle_one_iteration <- function(X, y, beta.k, beta.old)
{
  b_old2 <- beta.old
  eta <- X%*% beta.k
  p  <- 1/(1+exp(-eta))
  W <- as.numeric(p*(1-p))
  z <- eta + ((y - p)/W)
  XtX <- crossprod(X,diag(W)%*%X)
  detV <- det(XtX)
  if(is.na(detV)) return(b_old2)
  if(detV==0) return(b_old2)
  eXtX <- eigen(XtX)$values
  CN <- sqrt(abs(max(eXtX)/min(eXtX)))
  if(is.nan(CN)) return(c(b_old2))
  Xtz <- crossprod(X,W*z)
  if(CN >= CN0) return(c(b_old2))     
  else          beta.k <- solve(XtX,Xtz)
  if(any(is.nan(beta.k))) return(c(b_old2))
  return(c(beta.k))
}


Lamda_Ridge=function(P,B){
  Lamda=c((P+1)/(crossprod(B,B)))
  sign_la <- sign(Lamda)
  if (abs(Lamda) < tho0) {
    Lamda <-  sign_la*tho0
  }
  return(Lamda)
}


Lamda_Liu=function(P,B){
  Lamda=c((P+1)/(crossprod(B,B)))
  sign_la <- sign(Lamda)
 
  if (abs(Lamda) < tho0) {
    Lamda <-  sign_la*tho0
  }
  return(Lamda)
}


dOptFix <- function(X,la,Bhat,lb,ub)
{
  MSE=c()
  pp <- ncol(X)
  IPP <- diag(pp)
  eta <- X%*% Bhat
  p  <- 1/(1+exp(-eta))
  W <- as.numeric(p*(1-p))
  d <- seq(lb,ub,0.01)
  XtX <- crossprod(X,diag(W)%*%X)
  V1 <- XtX+(la*IPP)
  detV1 <- det(V1)
  if(is.na(detV1) || detV1==0)
  {
    dopt <- 0
    return(dopt)
  }
  sV1 <- solve(V1)
  V3 <- XtX
  V4 <- crossprod(X,W*p)
  for (i in 1:length(d))
  {
    V2<- XtX-(d[i]*IPP)
    part1=sum(diag(sV1%*%V2%*%sV1%*%V3%*%sV1%*%V2%*%sV1))
    part2=sV1%*%V2%*%sV1%*%V4
    part3=sum((part2-Bhat)^2)
    MSE[i]=part1+part3
  }
  Min_MSE=which.min(MSE)       
  dopt=d[Min_MSE]
  return(dopt)
}



irwls_Ridge_one_iteration <- function(X, y,La ,beta.k, beta.old)
{
  pp <- ncol(X)
  IPP <- diag(pp) 
  b_old2 <- beta.old
  eta <- X%*% beta.k
  p  <- 1/(1+exp(-eta))
  W <- as.numeric(p*(1-p))
  z <- eta + ((y - p)/W)
  XtX <- crossprod(X,diag(W)%*%X)
  V=XtX+La*IPP
  detV <- det(V)
  if(is.na(detV)) return(b_old2)
  if(detV==0) return(b_old2)
  eV <- eigen(V)$values
  CN <- sqrt(abs(max(eV)/min(eV)))
  if(is.nan(CN)) return(b_old2)
  if(CN >= CN0) return(b_old2)    
  Xtz <- crossprod(X,W*z)
  beta.k <- solve(V,Xtz)
  if(any(is.nan(beta.k))) return(b_old2)
  return(c(beta.k))
}

irwls_Liu_one_iteration_rid <- function(X, y, La ,dFix ,beta.k, beta.old)
{
  pp <- ncol(X)
  IPP <- diag(pp) 
  b_old2 <- beta.old
  eta <- X%*% beta.k
  p  <- 1/(1+exp(-eta))
  W <- as.numeric(p*(1-p))
  z <- eta + ((y - p)/W)
  XtX <- crossprod(X,diag(W)%*%X)
  eXtX <- eigen(XtX)$values
  V=XtX+La*IPP
  detV <- det(V)
  if(is.na(detV)) return(b_old2)
  if(detV==0) return(b_old2)
  eV <- eigen(V)$values
  CN <- sqrt(abs(max(eV)/min(eV)))
  if(is.nan(CN)) return(b_old2)
  if(CN >= CN0) return(b_old2)     
  Xtz <- crossprod(X,W*z)
  CNxtx <- sqrt(abs(max(eXtX)/min(eXtX)))
  if(is.nan(CNxtx)) return(b_old2)
  if(CNxtx >= CN0) return(b_old2)   
  B_Hat <- solve(V,Xtz)
  if(any(is.nan(B_Hat))) return(b_old2)
  V1=XtX-(dFix*IPP)
  beta.k=solve(V,V1%*%B_Hat)
  if(any(is.nan(beta.k))) return(b_old2)
  return(c(beta.k))
}



ll <- function(x,y,pi,beta)
{
  n <- dim(x)[1]
  L <- length(pi)
  LL_Matrix <- matrix(data=NA, nrow=n, ncol=L)
  for (j in 1:L) 
  {
    for (i in 1:n) 
    {
      P_j <- etaFun(x[i,],beta[j,])
      Mat_ij <- pi[j]*(P_j^y[i])*((1-P_j)^(1-y[i]))
      LL_Matrix[i,j] <- Mat_ij
    }
  }
  Sum_Rows <- rowSums(LL_Matrix)
  Log_Sum_Rows <- sum(log(Sum_Rows))
  return(Log_Sum_Rows)
}


em_ml <-function(epsilon,x,y,beta.0,beta.old,pi.0,pi.old,maxit_EM,tol_irwls,printout=F)
{
  pp <- dim(x)[2]
  M <- length(pi.0)  
  Beta_Mle <- matrix(data=NA, nrow=M, ncol=pp)
  convergence<-F
  beta.k <- beta.0
  pi.k  <- pi.0
  for(k in 1:maxit_EM)
  {
    if(any(is.na(beta.k)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_vec <- c(pi.old,MSE,MSE_Beta,k,101)
      ret <- list(k=k,pi=round(pi_vec,3),beta=beta.old)
      return(ret)
    }
    
    if(any(is.na(pi.k)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_vec <- c(pi.old,MSE,MSE_Beta,k,102)
      ret <- list(k=k,pi=round(pi_vec,3),beta=beta.old)
      return(ret)
    }
    
    tau <- Design_Tau(x,y,beta.k,pi.k) 
    if(any(is.na(tau)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_vec <- c(pi.old,MSE,MSE_Beta,k,103)
      ret <- list(k=k,pi=round(pi_vec,3),beta=beta.old)
      return(ret)
    }
    Z <- Zstoc(tau=tau)
    if(any(is.na(Z)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      pi_vec <- c(pi.old,MSE,MSE_Beta,k,104)
      ret <- list(k=k,pi=round(pi_vec,3),beta=beta.old)
      return(ret)
    }
    
    for (j in 1:ncol(Z)) 
    {
      zInd <- Z[,j]==1
      if(sum(zInd)==1)
      {
        MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
        MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
        if(k==1) return(list(k=k,pi=c(pi.old,MSE,MSE_Beta,k,1),beta=beta.old))
        pi_vec <- c(pi.old,MSE,MSE_Beta,k,105)
        ret <- list(k=k,pi=round(pi_vec,3),beta=beta.old)
        return(ret)
      }
      beta_mle <- irwls_mle_one_iteration(X=x[zInd,],y=y[zInd],
                                           beta.k=beta.k[j,],beta.old=beta.old[j,])
      Beta_Mle[j,] <- beta_mle
    }
    pi.new <- colMeans(Z)
    beta.new <- Beta_Mle
    if(printout==T) print(cbind(pi.new,beta.new),digits=3)
    changeValueBeta <- sqrt(sum(diag(crossprod(t(beta.new-beta.k)))))
    changeValuePi   <- sqrt((pi.new[1]-pi.k[1])^2)
    changeValuell <- abs(ll(x,y,pi.new,beta.new)-ll(x,y,pi.k,beta.k)) 
    if(changeValuell < tol_irwls)    break
    pi.old <- pi.k
    pi.k <- pi.new 
    beta.old <- beta.k
    beta.k <- beta.new
  } 
  
  MSE <- .msepi_one_iteration(pi.new[1],pi0[1])
  MSE_Beta <- .msebeta_one_iteration(beta.new,Beta0)
  pi_vec <- c(pi.new,MSE,MSE_Beta,k,100)
  ret <- list(k=k,pi=round(pi_vec,3),beta=beta.new)
  return(ret)
}


em_ridge <-function(epsilon,x,y,beta.0,beta.old,pi.0,pi.old,maxit_EM,tol_irwls,Beta_Hat,printout=F)
{
  pp <- dim(x)[2]
  M <- length(pi.0)  
  Beta_Ridge <- matrix(data=NA, nrow=M, ncol=pp)
  Lamda <- c()
  convergence<-F
  beta.k <- beta.0
  pi.k  <- pi.0
  for(k in 1:maxit_EM)
  {
    if(any(is.na(beta.k)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_Lamda <- c(pi.old,Lamda,MSE,MSE_Beta,k,101)
      ret <- list(k=k,pi=round(pi_Lamda,3),beta=beta.old)
      return(ret)
    }
    
    if(any(is.na(pi.k)))
    {
      
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_Lamda <- c(pi.old,Lamda,MSE,MSE_Beta,k,102)
      ret <- list(k=k,pi=round(pi_Lamda,3),beta=beta.old)
      return(ret)
    }
    tau <- Design_Tau(x,y,beta.k,pi.k) 
    if(any(is.na(tau)))
    {
     
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_Lamda <- c(pi.old,Lamda,MSE,MSE_Beta,k,103)
      ret <- list(k=k,pi=round(pi_Lamda,3),beta=beta.old)
      return(ret)
    }
    Z <- Zstoc(tau=tau)
    if(any(is.na(Z))) 
    {
      
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_Lamda <- c(pi.old,Lamda,MSE,MSE_Beta,k,104)
      ret <- list(k=k,pi=round(pi_Lamda,3),beta=beta.old)
      return(ret)
    }
    
    for (j in 1:ncol(Z)) 
    {
      LamdaJ <- Lamda_Ridge(pp,Beta_Hat[j,])
      zInd <- Z[,j]==1
      if(sum(zInd)==1)
      {
        MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
        MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
        if(k==1) return(list(k=k,pi=c(pi.old,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
        pi_Lamda <- c(pi.old,Lamda,MSE,MSE_Beta,k,105)
        ret <- list(k=k,pi=round(pi_Lamda,3),beta=beta.old)
        return(ret)
      }
      beta_ridge <- irwls_Ridge_one_iteration(X=x[zInd,],y=y[zInd],La=LamdaJ,
                                          beta.k=beta.k[j,],beta.old=beta.old[j,])
      Beta_Ridge[j,] <-  beta_ridge
      Lamda[j] <-LamdaJ
    }
    pi.new <- colMeans(Z)
    beta.new <- Beta_Ridge
    if(printout==T) print(cbind(pi.new,beta.new),digits=3)
    changeValueBeta <- sqrt(sum(diag(crossprod(t(beta.new-beta.k)))))
    changeValuePi   <- sqrt((pi.new[1]-pi.k[1])^2)
    changeValuell <- abs(ll(x,y,pi.new,beta.new)-ll(x,y,pi.k,beta.k)) 
    if(changeValuell < tol_irwls)    break
    pi.old <- pi.k
    pi.k <- pi.new 
    beta.old <- beta.k
    beta.k <- beta.new
  }
  
  MSE <- .msepi_one_iteration(pi.new[1],pi0[1])
  MSE_Beta <- .msebeta_one_iteration(beta.new,Beta0)
  pi_Lamda <- c(pi.new,Lamda,MSE,MSE_Beta,k,100)
  ret <- list(k=k,pi=round(pi_Lamda,3),beta=beta.new)
  return(ret)
}


em_Liu <-function(epsilon,x,y,beta.0,beta.old,pi.0,pi.old,maxit_EM,tol_irwls,Beta_Hat,printout=F)
{
  pp <- dim(x)[2]
  M <- length(pi.0)  
  Beta_Liu <- matrix(data=NA, nrow=M, ncol=pp)
  Lamda <- c()
  dopt <- c()
  convergence<-F
  beta.k <- beta.0
  pi.k  <- pi.0
  for(k in 1:maxit_EM)
  {
    if(any(is.na(beta.k)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,0,0,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_Lamda_dopt <- c(pi.old,Lamda,dopt,MSE,MSE_Beta,k,101)
      ret <- list(k=k,pi=round(pi_Lamda_dopt,3),beta=beta.old)
      return(ret)
    }
    
    if(any(is.na(pi.k)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,0,0,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_Lamda_dopt <- c(pi.old,Lamda,dopt,MSE,MSE_Beta,k,102)
      ret <- list(k=k,pi=round(pi_Lamda_dopt,3),beta=beta.old)
      return(ret)
    }
    
    tau <- Design_Tau(x,y,beta.k,pi.k) 
    if(any(is.na(tau)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,0,0,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_Lamda_dopt <- c(pi.old,Lamda,dopt,MSE,MSE_Beta,k,103)
      ret <- list(k=k,pi=round(pi_Lamda_dopt,3),beta=beta.old)
      return(ret)
    }
    Z <- Zstoc(tau=tau)
    if(any(is.na(Z)))
    {
      MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
      MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
      if(k==1) return(list(k=k,pi=c(pi.old,0,0,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
      pi_Lamda_dopt <- c(pi.old,Lamda,dopt,MSE,MSE_Beta,k,104)
      ret <- list(k=k,pi=round(pi_Lamda_dopt,3),beta=beta.old)
      return(ret)
    }
    
    for (j in 1:ncol(Z)) 
    {
      zInd <- Z[,j]==1
      if(sum(zInd)==1)
      {
        MSE <- .msepi_one_iteration(pi.old[1],pi0[1])
        MSE_Beta <- .msebeta_one_iteration(beta.old,Beta0)
        if(k==1) return(list(k=k,pi=c(pi.old,0,0,0,0,MSE,MSE_Beta,k,1),beta=beta.old))
        pi_Lamda_dopt <- c(pi.old,Lamda,dopt,MSE,MSE_Beta,k,105)
        ret <- list(k=k,pi=round(pi_Lamda_dopt,3),beta=beta.old)
        return(ret)
      }
      
      LamdaJ <- Lamda_Liu(pp,Beta_Hat[j,])
      dFixJ <- dOptFix(X=x[zInd,],la=LamdaJ,Bhat=Beta_Hat[j,],lb=Lower0,ub=Upper0)
      beta_Liu <- irwls_Liu_one_iteration_rid(X=x[zInd,],y=y[zInd],La=LamdaJ,dFix=dFixJ,
                                beta.k=beta.k[j,],beta.old=beta.old[j,])
      Beta_Liu[j,] <-  beta_Liu
      Lamda[j] <- LamdaJ
      dopt[j] <- dFixJ 
    }
    pi.new <- colMeans(Z)
    beta.new <- Beta_Liu
    if(printout==T) print(cbind(pi.new,beta.new),digits=3)
    changeValueBeta <- sqrt(sum(diag(crossprod(t(beta.new-beta.k)))))
    changeValuePi   <- sqrt((pi.new[1]-pi.k[1])^2)
    changeValuell <- abs(ll(x,y,pi.new,beta.new)-ll(x,y,pi.k,beta.k))
    if(changeValuell < tol_irwls)    break
    pi.old <- pi.k
    pi.k <- pi.new 
    beta.old <- beta.k
    beta.k <- beta.new
  }
  
  MSE <- .msepi_one_iteration(pi.new[1],pi0[1])
  MSE_Beta <- .msebeta_one_iteration(beta.new,Beta0)
  pi_Lamda_dopt <- c(pi.new,Lamda,dopt,MSE,MSE_Beta,k,100)
  ret <- list(k=k,pi=round(pi_Lamda_dopt,3),beta=beta.new)
  return(ret)
}



.mseBeta <- function(Mhat,Btrue)
{
  dif1 <- sqrt((Mhat-Btrue)^2)
  dif2 <- apply(dif1, 3, sum)
  meanBeta <- round(mean(dif2),3)
  quanBeta <- round(quantile(dif2, probs=c(0.025,0.5,0.975)),3)
  quanlen <- quanBeta[3]-quanBeta[1]
  tab <- c(meanBeta,quanBeta[2],quanBeta[1],quanBeta[3],quanlen)
  return(tab)
}



.msepi <- function(P_hat,P_true)
{
  dif1 <- sqrt((P_hat-P_true)^2)
  mean_pi <- round(mean(dif1),3)
  quan_pi <- round(quantile(dif1, probs=c(0.025,0.5,0.975)),3)
  quanlen <- quan_pi[3]-quan_pi[1]
  tab <- c(mean_pi,quan_pi[2],quan_pi[1],quan_pi[3],quanlen)
  return(tab)
}



Simulation <- function(n,p,rho,phi,epsilon,M,Beta,beta.0,beta.old,pi,pi.0,pi.old,maxit_EM,tol_irwls,printout=F)
{
  resArray_LS <-resArray_Ridge <- resArray_Liu <- array(NA,dim=c(2,5,Nsim))
  MO_LS_pi <- matrix(NA, nrow = Nsim, ncol = length(pi)*3)
  MO_Ridge_pi <- matrix(NA, nrow = Nsim, ncol = length(pi)*3+2)
  MO_Liu_pi <- matrix(NA, nrow = Nsim, ncol = length(pi)*4+2)
  for (j in 1:Nsim)
  {
    cat("j = ",j)
    x <- Design_Matrix(n=n,p=p,rho=rho,phi=phi)
    Yres <- Design_Response_Mixture(x=x,beta=Beta,pi=pi,M=M)
    y <- Yres[,1]
    
  
    EM_Result_LS <- em_ml(epsilon=epsilon,x=x,y=y,beta.0=beta.0,
                          beta.old=beta.old,pi.0=pi.0,pi.old=pi.old,maxit_EM=maxit_EM,
                          tol_irwls=tol_irwls,printout=F)
    B_ml <- EM_Result_LS$beta
    P_ml <- EM_Result_LS$pi
    K_LS <- EM_Result_LS$k
    print(K_LS)
    resArray_LS[,,j] <- B_ml
    MO_LS_pi[j,] <- P_ml
    
   
    EM_Result_Ridge <-em_ridge(epsilon=epsilon_em0,x=x,y=y,beta.0=Beta.01,
                            beta.old=Beta.02,pi.0=pi.01,pi.old=pi.02,maxit_EM=maxit_em0,
                            tol_irwls=tol_irwls0,Beta_Hat=B_ml,printout=F)
     
     B_ridge <- EM_Result_Ridge$beta
     P_ridge <- EM_Result_Ridge$pi
     K_Ridge <- EM_Result_Ridge$k
     resArray_Ridge[,,j] <- B_ridge
     MO_Ridge_pi[j,] <- P_ridge 
     
     
     EM_Result_Liu <-em_Liu(epsilon=epsilon_em0,x=x,y=y,beta.0=Beta.01,
                                beta.old=Beta.02,pi.0=pi.01,pi.old=pi.02,maxit_EM=maxit_em0,
                                tol_irwls=tol_irwls0,Beta_Hat=B_ridge,printout=F)
     B_Liu <- EM_Result_Liu$beta
     P_Liu <- EM_Result_Liu$pi
     K_Liu <- EM_Result_Liu$k
     resArray_Liu[,,j] <- B_Liu
     MO_Liu_pi[j,] <- P_Liu 
    
    
  }
  return(list(MO_LS_Beta=resArray_LS,MO_LS_pi=MO_LS_pi,
              MO_Ridge_Beta=resArray_Ridge,MO_Ridge_pi=MO_Ridge_pi,
              MO_Liu_Beta=resArray_Liu,MO_Liu_pi=MO_Liu_pi))
}




Wrapping <- function(M_hat_LS,M_hat_Ridge,M_hat_Liu,B_true,Pi_hat_LS,Pi_hat_Ridge,Pi_hat_Liu,Pi_true)
{
  naIndLS <- which(!is.na(M_hat_LS[1,1,]))
  M_hat_LS <- M_hat_LS[,,naIndLS]
  Barray <- array(B_true,dim=c(2,5,Nsim))
  EMSE_LS_Beta     <- .mseBeta(Mhat =  M_hat_LS,Btrue = Barray)
  EMSE_LS_Pi     <- .msepi(P_hat =  Pi_hat_LS[,1],P_true = Pi_true[1])
  
  EMSE_Ridge_Beta     <- .mseBeta(Mhat =  M_hat_Ridge,Btrue = Barray)
  EMSE_Ridge_Pi     <- .msepi(P_hat =  Pi_hat_Ridge[,1],P_true = Pi_true[1])
  
  EMSE_Liu_Beta     <- .mseBeta(Mhat =  M_hat_Liu,Btrue = Barray)
  EMSE_Liu_Pi     <- .msepi(P_hat =  Pi_hat_Liu[,1],P_true = Pi_true[1])
  
  tabMSE <- rbind(EMSE_LS_Beta,EMSE_LS_Pi,EMSE_Ridge_Beta,EMSE_Ridge_Pi,EMSE_Liu_Beta,EMSE_Liu_Pi)
  colnames(tabMSE) <- c("mean","median","5%","95%","length")
  rownames(tabMSE) <- c("LS_Beta","LS_Pi","Ridge_Beta","Ridge_Pi","Liu_Beta","Liu_Pi")
  return(tabMSE)
}



Error_Measurment<-function(Y_test,Y_hat)
{
  Actual<-c(Y_test)
  Prediction<-c(Y_hat)
  
  TP=FP=FN=TN<-0
  for(i in 1:length(Actual)) 
  {
    if(Actual[i]==1&&Prediction[i]==1)       TP=TP+1 
    else if(Actual[i]==1&&Prediction[i]==0)  FN=FN+1
    else if (Actual[i]==0&&Prediction[i]==1) FP=FP+1
    else TN=TN+1
    
  }
  P<-TP+FN
  N<-FP+TN
  Error<-(FP+FN)/(P+N)
  Sensitivity <- TP/(TP+FN)
  Specificity <- TN/(TN+FP) 
  return(list(Error=Error,Sen=Sensitivity,Spe=Specificity))
}


Generate_Testing <- function(n,p,rho,phi,Beta,pi,M)
{
  x <- Design_Matrix(n=n,p=p,rho=rho,phi=phi)
  Yres <- Design_Response_Mixture(x=x,beta=Beta,pi=pi,M=M)
  y <- Yres[,1]
  
  return(list(x=x,y=y))
}



.mse_err <- function(err)
{
  dif1 <- err
  mean_err <- round(mean(dif1),2)
  quan_err <- round(quantile(dif1, probs=c(0.025,0.5,0.975)),2)
  quanlen <- quan_err[3]-quan_err[1]
  tab <- c(mean_err,quan_err[2],quan_err[1],quan_err[3],quanlen)
  return(tab)
}


Testing <- function(MO_LS,MO_Ridge,MO_Liu,MO_Pi_LS,MO_Pi_Ridge,MO_Pi_Liu,M)
{
  Err_LS <- Err_Ridge <- Err_Liu <- c()
  Sen_LS <- Sen_Ridge <- Sen_Liu <- c()
  Spe_LS <- Spe_Ridge <- Spe_Liu <- c()
  
  for (i in 1:Nsim) 
  {
    
    Test_Data <- Generate_Testing(n=n0test,p=p0,rho=rho0t,phi=phi0t,Beta=Beta0,pi=pi0,M=M0)
    X_test=Test_Data$x
    Y_test=Test_Data$y
    
   
    
    Yres_LS <- Design_Response_Mixture(x=X_test,beta=MO_LS[,,i],pi=MO_Pi_LS[i,],M=M)
    Y_hat_LS <- Yres_LS[,1]
    Class_LS <- Error_Measurment(Y_test,Y_hat_LS)
    Err_LS[i] <- Class_LS$Error
    Sen_LS[i] <- Class_LS$Sen
    Spe_LS[i] <- Class_LS$Spe
   
    
    Yres_Ridge <- Design_Response_Mixture(x=X_test,beta=MO_Ridge[,,i],pi=MO_Pi_Ridge[i,],M=M)
    Y_hat_Ridge <- Yres_Ridge[,1]
    Class_Ridge <- Error_Measurment(Y_test,Y_hat_Ridge)
    Err_Ridge[i] <- Class_Ridge$Error
    Sen_Ridge[i] <- Class_Ridge$Sen
    Spe_Ridge[i] <- Class_Ridge$Spe
   
    Yres_Liu <- Design_Response_Mixture(x=X_test,beta=MO_Liu[,,i],pi=MO_Pi_Liu[i,],M=M)
    Y_hat_Liu <- Yres_Liu[,1]
    Class_Liu <- Error_Measurment(Y_test,Y_hat_Liu)
    Err_Liu[i] <- Class_Liu$Error
    Sen_Liu[i] <- Class_Liu$Sen
    Spe_Liu[i] <- Class_Liu$Spe
    
  }
  
  
  
  Err_LS <- .mse_err(Err_LS)
  Err_Ridge <- .mse_err(Err_Ridge)
  Err_Liu <- .mse_err(Err_Liu)
  
  
  
  Sen_LS <- .mse_err(Sen_LS)
  Sen_Ridge <- .mse_err(Sen_Ridge)
  Sen_Liu <- .mse_err(Sen_Liu)
  
 
  
  Spe_LS <- .mse_err(Spe_LS)
  Spe_Ridge <- .mse_err(Spe_Ridge)
  Spe_Liu <- .mse_err(Spe_Liu)
  
  tabMSE <- rbind(Err_LS,Err_Ridge,Err_Liu,Sen_LS,Sen_Ridge,Sen_Liu,Spe_LS,Spe_Ridge,Spe_Liu)
  colnames(tabMSE) <- c("mean","median","5%","95%","length")
  rownames(tabMSE) <- c("Error_LS","Error_Ridge","Error_Liu","Sen_LS","Sen_Ridge","Sen_Liu","Spe_LS","Spe_Ridge","Spe_Liu")
  return(tabMSE)
}



Sim_Result=Simulation(n=n0t,p=p0,rho=rho0t,phi=phi0t,epsilon=epsilon_em0,M=M0,
                      Beta=Beta0,beta.0=Beta.01,beta.old=Beta.02,
                      pi=pi0,pi.0=pi.01,pi.old=pi.02,maxit_EM=maxit_em0,
                      tol_irwls=tol_irwls0)

MO_LS <- Sim_Result$MO_LS_Beta
MO_Pi_Sim <- Sim_Result$MO_LS_pi
MO_Pi_LS <- MO_Pi_Sim[,1:2]

MO_Ridge <- Sim_Result$MO_Ridge_Beta
MO_Pi_Ridge_lamda <- Sim_Result$MO_Ridge_pi
MO_Pi_Ridge <- MO_Pi_Ridge_lamda[,1:2]

MO_Liu <- Sim_Result$MO_Liu_Beta
MO_Pi_Liu_lamda_dopt <- Sim_Result$MO_Liu_pi
MO_Pi_Liu <-MO_Pi_Liu_lamda_dopt[,1:2]


MSE_Result <-Wrapping(MO_LS,MO_Ridge,MO_Liu,Beta0,MO_Pi_LS,MO_Pi_Ridge,MO_Pi_Liu,pi0)
MSE_Result


Test_Result=Testing(MO_LS,MO_Ridge,MO_Liu,MO_Pi_LS,MO_Pi_Ridge,MO_Pi_Liu,M=M0)
Test_Result
