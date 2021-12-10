#direct console output to a file
#sink("output.txt", append=FALSE, split=TRUE)
#remove all R objects  from memory
rm(list = ls())


#set default lib path
.libPaths("C:/R packs")
#load libs
library(plyr)
library(modeldata)
library(sdcMicro)
library(kmed)
library(gtools)
library(e1071)
library(StatMatch)
library(dplyr)
library(infotheo)
library(xts)
library(quantmod)
library(psych)
library(arules)
library(modeldata)
library(lsr)
library(MALDIquant)
library(aricode)
library(praznik)
library(shipunov)
library(varrank)
library(randomForest)
library(caret)
library(rpart) 
library(data.table)
library(scclust)



###########These variables need to be changed per file#######
#set working directory
#setwd("C:/Users\senn\Desktop\test\PA_N_QID")



df_path <<-"C:/Users/senn/Desktop/test/NEWIMP/Data/"
res_path <<-res_path <<-"C:/Users/senn/Desktop/test/NEWIMP/QID/MASKED/Thesis/SUP/"


masked_df="heart"
df_list <<- paste0(masked_df,'.csv')
dfname <<- masked_df

MA_list <- unlist(list(3, 5, 10, 25))


if (masked_df=="heart")
{
  #heart
  var_list<<-c('N','C','C','N','N','C','C','N','C','N','C','C','C')
  QID_list<<-c(1,2,5)
  
}else if (masked_df=="abalone")
{
  
  #Abalone
  var_list<<-c('C','N','N','N','N','N','N','N')
  QID_list<<-c(1,2,5,7)
  MA_list <- unlist(list(5,10,50,100))
  
}else if (masked_df=="gc")
{
  
  #GC german credit
  var_list<<-c('C','N','C','C','N','C','C','N','C','C','N','C','N','C','C','N','C','N','C','C','C','C','C','C')
  QID_list<<-c(2,3,4,7,10)
  #MA_list <- unlist(list(5,50,100,200))
  
  
}else if (masked_df=="cmc")
{
  
  var_list<<-c('N','C','C','N','C','C','C','C','C')
  QID_list<<-c(1,2,4,8)
  #MA_list <- unlist(list(5,50,100,200))
  
  
}else if (masked_df=="CTG")
{
  
  #CTG
  var_list<<-c('N','N','N','N','N','N','N','N','N','C','C','N','N','N','N','N','N','N','N','N','N','C')
  QID_list<<-c(4,7,8,10)
  #MA_list <- unlist(list(5,50,100,200))
  
  
}else if (masked_df=="adult")
{
  
  #Adult
  var_list<<-c('N','C','N','C','N','C','C','C','C','C','N','N','N','C')
  QID_list<<-c(1,2,3,5,6,7)
  #MA_list <- unlist(list(5,50,100,200))
  
}else if (masked_df=="mm")
{
  #Mamographic
  var_list<<-c('C','N','C','C','C')
  QID_list<<-c(1,2,3,4)
  #MA_list <- unlist(list(5,50,100,200))
  
}



FIN_QID<-c()                                                                                                                                                                                                                                                                                                                                                                                                                                             
unique_list<-c()
entropy_val<<-c()
zero_entropy_val<<-c()
num_rounds<-1
uniqueness_list<-c(0,1)

qid_type<-c('specified','all')#,'all'
dist_list<-c('gower')#,'ahmad'
group_list<<-c(1)


c_size_a_h<<-list()
c_size_g_h<<-list()
c_size_a_m<<-list()
c_size_g_m<<-list()

################################################
#           Probabilistic k-ANN                #
################################################

newdist <- function(data, col = col, colnum)
{
  u_vals <<- c(unique(data[1]))[[1]]
  nvar <- 1:col
  n <- length(levels(as.factor(data[,colnum])))
  
  var <- prob <- vector("list", (col-1))
  for (i in 1:(col-1)) 
  {
    var[[i]] <- table(data[,nvar[-colnum][i]],data[,colnum])
    #print(table(data[,nvar[-colnum][i]],data[,colnum]))
    
    prob[[i]] <- var[[i]]/matrix(colSums(var[[i]]),
                                 nrow=nrow(var[[i]]), ncol = ncol(var[[i]]),
                                 byrow = TRUE)
    #print(var[[i]]/matrix(colSums(var[[i]]),
    #                      nrow=nrow(var[[i]]), ncol = ncol(var[[i]]),
    #                      byrow = TRUE))
  }
  
  probmat <- do.call(rbind,prob)
  #print(probmat)
  matnew <- matrix(0, nrow = n, ncol = n)
  #print(matnew)
  rownames(matnew) <- colnames(matnew) <- 1:n
  #print(matnew)
  
  for (i in 1:n) 
  {
    for (j in 1:n) 
    {
      matnew[i,j] <- (sum(apply(probmat[,c(i,j)], 1, max))-(col-1))/(col-1)
    }
  }
  
  rownames(matnew) <- colnames(matnew) <- sort(u_vals)
  #print(matnew)
  
  return(matnew)
}

data_permutation <- function(data_full, qids, rec_list)
{ 
  entropy_vec<-c()
  
  data_for_swap<-data_full 
  
  
  #QIDs
  df_qid<-data_for_swap[c(qids)]
  
  
  if (sum(names(data_for_swap) %in% qids)==ncol(data_for_swap))
  {
    NQID=0
    print("All variables are considered as QIDs")
    
  }else
  {
    NQID=1
    #print("Only some variables are considered as QIDs")
    #NonQIDs
    nonqid_vars <- setdiff(names(data_for_swap),qids)
    df_non_qid<-data_for_swap[c(nonqid_vars)]
  }
  
  
  
  ###########swapping #######   
  fin_dataFile<-data.frame()
  int_dataFile <- data.frame()
  
  
  for (n in 1:length(rec_list))
  {
    
    #records fall into one EC
    rlist_names <- as.character(rec_list[[n]])
    
    if(NQID==0)
    {
      #All qid
      k_part_qid <- df_qid[rlist_names,]
    }
    else
    {
      #some qid
      
      k_part_qid <- df_qid[rlist_names,]
      k_part_nqid <- df_non_qid[rlist_names,]
      nqid_col <-ncol(df_non_qid)
      
    }
    
    #get row names
    vec_idx=as.numeric(row.names(k_part_qid))
    
    ######No Grouping##################
    ######Start permutation of data####
    g=1
    for (y in names(data_for_swap))
    {
      #cat("processing variable ",y,"\n")
      
      ori_idx<-rlist_names
      per_idx<-ori_idx
      
      if (y %in%qids)
      {
        #cat("QID : ",y,"\n")
        
        cnt=1
        while (identical(per_idx,ori_idx)) 
        {
          if(cnt <=10)
          {
            
            r_names<-rownames(k_part_qid)
            r_names_permutation<-sample(r_names)
            per_idx<-as.numeric(r_names_permutation)
            cnt=cnt+1
          }
          else
          {
            break;
            
          }
          
        }
        
        permuted_vec <- k_part_qid[r_names_permutation,y]
      }
      else
      {
        
        if(nqid_col==1)
        {
          permuted_vec <- k_part_nqid
        }else
        {
          permuted_vec <- k_part_nqid[rlist_names,y]
        }
        
        #cat("Entropy :", entropy.data(table(permuted_vec)),"\n")
        entropy_vec<-append(entropy_vec,entropy.data(table(permuted_vec)))
      }
      
      
      if(g==1)
      {
        tmp_dataFile<- permuted_vec
      }else
      {
        tmp_dataFile<- cbind(tmp_dataFile,permuted_vec)
      }
      
      
      g=g+1
    }
    
    
    ######with Grouping##################
    
    
    #add new rows to datafile
    int_dataFile <- rbind(int_dataFile,tmp_dataFile)
    
  }
  
  #print("Add all the records in the k-anonymized record list")
  #print("Rearrange  the data columns")
  fin_dataFile <- int_dataFile
  entropy_val<<-append(entropy_val,mean(entropy_vec))
  zero_entropy_val<<-append(zero_entropy_val,sum(entropy_vec == 0)/length(entropy_vec))
  
  
  return(fin_dataFile)
}


data_permutation_with_Group <- function(data_full, qids, group, rec_list)
{ 
  print("data_permutation_with_Group")
  
  klab <- paste('V', c(colnames(data_full)), sep = '')
  colnames(data_full)<-klab
  
  qids<-paste('V', c(qids), sep = '')
  
  data_for_swap<-data_full 
  
  
  #QIDs
  df_qid<-data_for_swap[c(qids)]
  
  
  
  if (sum(names(data_for_swap) %in% qids)==ncol(data_for_swap))
  {
    NQID=0
    print("All variables are considered as QIDs")
    
  }else
  {
    NQID=1
    print("Only some variables are considered as QIDs")
    #NonQIDs
    nonqid_vars <- setdiff(names(data_for_swap),qids)
    df_non_qid<-data_for_swap[c(nonqid_vars)]
  }
  
  
  #Grouping varriables
  
  if (length(qids)>2)
  {
    print("qid>2")
    
    #MI computation
    lab <- paste('V', c(1:(ncol(data_full)-1)), sep = '')
    MI<-MI_Info(data_full)
    MI_df<-data.frame(lab,MI)
    MI_df<-MI_df[order(MI_df$MI),c(1,2)]
    
    MI_df <- subset(MI_df,  lab %in% qids)
    
    
    id_lab<-MI_df$lab
    
    #id_lab <- as.numeric(gsub("(\\D+)", "", id_lab))
    
    #print(id_lab)
    
    ns<-floor(length(names(df_qid))*0.5)
    
    variable_name_list<-split(id_lab, ceiling(seq_along(id_lab)/ns))
    
    f_len<-length(unlist(variable_name_list[length(variable_name_list)]))
    
    r<-1
    while (f_len==1)
    {
      f_len<-length(unlist(variable_name_list[length(variable_name_list)]))
      
      #print("final group size 1")
      ns<-ns-r
      variable_name_list<-split(id_lab, ceiling(seq_along(id_lab)/ns))
      r<-r+1
    }
    print(variable_name_list) 
    
  }else
  {
    
    
    ns<-(length(names(df_qid)))
    variable_name_list<-split(names(df_qid), ceiling(seq_along(names(df_qid))/ns))
  }  
  
  
  ###########swapping #######   
  fin_dataFile<-data.frame()
  int_dataFile <- data.frame()
  
  
  for (n in 1:length(rec_list))
  {
    #print(n)
    
    #records fall into one EC
    rlist_names <- as.character(rec_list[[n]])
    
    if(NQID==0)
    {
      #All qid
      #print("All qid")
      k_part_qid <- df_qid[rlist_names,]
    }
    else
    {
      #some qid
      #print("Some qid")
      
      k_part_qid <- df_qid[rlist_names,]
      k_part_nqid <- df_non_qid[rlist_names,]
      nqid_col <-ncol(df_non_qid)
      
      #print(k_part_qid)
    }
    
    #get row names
    vec_idx=as.numeric(row.names(k_part_qid))
    
    #klab <- paste('V', c(colnames(k_part_qid)), sep = '')
    #print(klab)
    #colnames(k_part_qid)<-klab
    #print(head(k_part_qid)) 
    #print("Start")
    ######Start permutation of data####
    
    ######No Grouping##################
    
    if (group==0)
    {
      #group_name<<-"_No_AB_"
      print("No group")
      print(names(data_for_swap))
      g<-1
      for (y in names(data_for_swap))
      {
        #cat("processing variable ",y,"\n")
        
        ori_idx<-rlist_names
        per_idx<-ori_idx
        
        if (y %in%qids)
        {
          cat("In QID : ",y,"\n")
          
          cnt=1
          while (identical(per_idx,ori_idx)) 
          {
            if(cnt <=10)
            {
              
              r_names<-rownames(k_part_qid)
              r_names_permutation<-sample(r_names)
              per_idx<-as.numeric(r_names_permutation)
              cnt=cnt+1
            }
            else
            {
              break;
              
            }
            
          }
          
          permuted_vec <- k_part_qid[r_names_permutation,y]
        }
        else
        {
          cat("Not in QID : ",y,"\n")
          
          if(nqid_col==1)
          {
            permuted_vec <- k_part_nqid
          }else
          {
            permuted_vec <- k_part_nqid[rlist_names,y]
          }
          
          
          #print(permuted_vec)
          
          #cat("Entropy :", entropy.data(table(permuted_vec)),"\n")
          #entropy_vec<-append(entropy_vec,entropy.data(table(permuted_vec)))
        }
        
        
        if(g==1)
        {
          tmp_dataFile<- permuted_vec
        }else
        {
          tmp_dataFile<- cbind(tmp_dataFile,permuted_vec)
        }
        
        #print(head(tmp_dataFile))
        g=g+1
      }
    }else
    {
      print("Grouped")
      
      g<-1
      permuted_vec<-c()
      for (z in 1:length(variable_name_list))
      {
        print(z)
        
        q_var<-c(t(data.frame(list(variable_name_list[z]))))
        
        print(q_var)
        
        df_q_grp<-df_qid[q_var]
        print(head(df_q_grp))
        
        print("******")
        
        ori_idx<-rlist_names
        per_idx<-ori_idx
        
        cnt=1
        while (identical(per_idx,ori_idx)) 
        {
          if(cnt <=10)
          {
            
            r_names<-rownames(k_part_qid)
            r_names_permutation<-sample(r_names)
            per_idx<-as.numeric(r_names_permutation)
            cnt=cnt+1
          }
          else
          {
            break;
            
          }
          
        }
        #print(r_names_permutation)
        #print(colnames(df_q_grp))
        #print(k_part_qid)
        
        permuted_vec <- k_part_qid[r_names_permutation,colnames(df_q_grp)]
        permuted_vec<-data.frame(permuted_vec)
        colnames(permuted_vec)<-colnames(df_q_grp)
        
        if(g==1)
        {
          tmp_dataFile<- permuted_vec
        }else
        {
          tmp_dataFile<- cbind(tmp_dataFile,permuted_vec)
        }
        
        
        g=g+1
        
      }
      
      #print("Done")
      
      #Add nqid and complete dataset
      if(NQID==0)
      {
        tmp_dataFile <- tmp_dataFile[, colnames(data_full)]
      }
      else
      {
        
        #######################################
        k_part_nqid <- data.frame(k_part_nqid)
        colnames(k_part_nqid)<-c(nonqid_vars)
        
        tmp_dataFile <- cbind(tmp_dataFile,k_part_nqid)
        
        #tlab <- paste('V', c(colnames(tmp_dataFile)), sep = '')
        
        #tmp_dataFile<-colnames(tlab)
        
        #print(tmp_dataFile)
        #print("col names")
        #print(colnames(data_full))
        
        #print("***")
        tmp_dataFile <- tmp_dataFile[, colnames(data_full)]
        
        print(tmp_dataFile)
      }
      
      
    }####group==1
    
    
    #add new rows to datafile
    int_dataFile <- rbind(int_dataFile,tmp_dataFile)
    
    
  }###each group of records
  
  
  
  fin_dataFile <- int_dataFile
  
  #lab <- paste('V', c(1:ncol(data_full)), sep = '')
  
  #fin_dataFile <- fin_dataFile[lab]
  
  
  #entropy_val<<-append(entropy_val,mean(entropy_vec))
  #zero_entropy_val<<-append(zero_entropy_val,sum(entropy_vec == 0)/length(entropy_vec))
  
  #print(head(fin_dataFile))
  
  return(fin_dataFile)
}


data_permutation_with_Group_new <- function(data_full, qids, group, rec_list)
{ 
  entropy_vec<-c()
  
  data_for_swap<-data_full 
  
  
  #QIDs
  df_qid<-data_for_swap[c(qids)]
  
  
  if (sum(names(data_for_swap) %in% qids)==ncol(data_for_swap))
  {
    NQID=0
    print("All variables are considered as QIDs")
    
  }else
  {
    NQID=1
    print("Only some variables are considered as QIDs")
    #NonQIDs
    nonqid_vars <- setdiff(names(data_for_swap),qids)
    df_non_qid<-data_for_swap[c(nonqid_vars)]
  }
  
  
  
  ###########swapping #######   
  fin_dataFile<-data.frame()
  int_dataFile <- data.frame()
  
  
  for (n in 1:length(rec_list))
  {
    
    #records fall into one EC
    rlist_names <- as.character(rec_list[[n]])
    
    if(NQID==0)
    {
      #All qid
      k_part_qid <- df_qid[rlist_names,]
    }
    else
    {
      #some qid
      
      k_part_qid <- df_qid[rlist_names,]
      k_part_nqid <- df_non_qid[rlist_names,]
      nqid_col <-ncol(df_non_qid)
      
    }
    
    #get row names
    vec_idx=as.numeric(row.names(k_part_qid))
    
    ######Start permutation of data####
    
    ######No Grouping##################
    
    if (group==0)
    {
      g<-1
      for (y in names(data_for_swap))
      {
        
        ori_idx<-rlist_names
        per_idx<-ori_idx
        
        if (y %in%qids)
        {
          
          cnt=1
          while (identical(per_idx,ori_idx)) 
          {
            if(cnt <=10)
            {
              
              r_names<-rownames(k_part_qid)
              r_names_permutation<-sample(r_names)
              per_idx<-as.numeric(r_names_permutation)
              cnt=cnt+1
            }
            else
            {
              break;
              
            }
            
          }
          
          permuted_vec <- k_part_qid[r_names_permutation,y]
        }
        else
        {
          
          if(nqid_col==1)
          {
            permuted_vec <- k_part_nqid
          }else
          {
            permuted_vec <- k_part_nqid[rlist_names,y]
          }
          
        }
        
        
        if(g==1)
        {
          tmp_dataFile<- permuted_vec
        }else
        {
          tmp_dataFile<- cbind(tmp_dataFile,permuted_vec)
        }
        
        
        g=g+1
      }
    }else
    {
      ######with Grouping##################
      ns<-floor(length(names(df_qid))*0.5)
      
      variable_name_list<-split(names(df_qid), ceiling(seq_along(names(df_qid))/ns))
      
      f_len<-length(unlist(variable_name_list[length(variable_name_list)]))
      
      r<-1
      while (f_len==1)
      {
        f_len<-length(unlist(variable_name_list[length(variable_name_list)]))
        
        ns<-ns-r
        variable_name_list<-split(names(df_qid), ceiling(seq_along(names(df_qid))/ns))
        r<-r+1
      }
      
      g<-1
      permuted_vec<-c()
      for (z in 1:length(variable_name_list))
      {
        z<-variable_name_list[[z]]
        df_q_grp<-df_qid[z]
        
        
        ori_idx<-rlist_names
        per_idx<-ori_idx
        
        cnt=1
        
        while (identical(per_idx,ori_idx)) 
        {
          if(cnt <=10)
          {
            
            r_names<-rownames(k_part_qid)
            r_names_permutation<-sample(r_names)
            per_idx<-as.numeric(r_names_permutation)
            cnt=cnt+1
          }
          else
          {
            break;
            
          }
          
        }
        
        permuted_vec <- k_part_qid[r_names_permutation,colnames(df_q_grp)]
        permuted_vec<-data.frame(permuted_vec)
        colnames(permuted_vec)<-colnames(df_q_grp)
        
        if(g==1)
        {
          tmp_dataFile<- permuted_vec
        }else
        {
          tmp_dataFile<- cbind(tmp_dataFile,permuted_vec)
        }
        
        
        g=g+1
        
      }
      
      
      #Add nqid and complete dataset
      if(NQID==0)
      {
        tmp_dataFile <- tmp_dataFile[, colnames(data_full)]
      }
      else
      {
        
        
        k_part_nqid <- data.frame(k_part_nqid)
        colnames(k_part_nqid)<-c(nonqid_vars)
        
        tmp_dataFile <- cbind(tmp_dataFile,k_part_nqid)
        
        tmp_dataFile <- tmp_dataFile[, colnames(data_full)]
        
      }
      
      
    }
    
    #add new rows to datafile
    int_dataFile <- rbind(int_dataFile,tmp_dataFile)
    
    
  }
  
  fin_dataFile <- int_dataFile
  
  
  return(fin_dataFile)
}

data_aggregation <-function (mean_rec, copy_with_target_df, k)
{
  
  cluster_list<-c()
  cluster_list_idx<-c()
  
  
  while(nrow(copy_with_target_df)> k-1)
  {
    
    ci<-c()
    ci_val<-c()
    tmp_df<-data.frame()
    
    colnames(copy_with_target_df)<-c("row","dist","target","diff")
    
    
    diff_df<-(abs(mean_rec-copy_with_target_df[2]))
    copy_with_target_df['diff'] = diff_df
    
    
    most_dist_val<-max(copy_with_target_df$diff)
    most_dist_indx<-match(most_dist_val,copy_with_target_df$diff)
    
    fin_idx<-as.numeric(as.character(copy_with_target_df[most_dist_indx,]$row))
    
    tmp_df<-rbind(tmp_df,copy_with_target_df[most_dist_indx,c(2,3)])
    
    ci<-append(ci,fin_idx)
    ci_val<-append(ci_val,most_dist_val)
    
    copy_with_target_df <- copy_with_target_df[-most_dist_indx,]
    
    
    while (length(ci)<k)
    {
      
      most_dist_val<-max(copy_with_target_df$diff)
      most_dist_indx<-match(most_dist_val,copy_with_target_df$diff)
      
      fin_idx<-as.numeric(as.character(copy_with_target_df[most_dist_indx,]$row))
      
      tmp_df<-rbind(tmp_df,copy_with_target_df[most_dist_indx,c(2,3)])
      
      ci<-append(ci,fin_idx)
      ci_val<-append(ci_val,most_dist_val)
      
      copy_with_target_df <- copy_with_target_df[-most_dist_indx,]
      
      
    }
    
    
    cluster_list<-append(cluster_list,list(ci_val))
    cluster_list_idx<-append(cluster_list_idx,list(ci))
    
  }
  
  #assign remaining values
  remaining_val<-append(cluster_list[length(cluster_list)][[1]],copy_with_target_df$diff)
  cluster_list[length(cluster_list)]<-list(remaining_val)
  
  remaining_idx<-append(cluster_list_idx[length(cluster_list_idx)][[1]],as.numeric(as.character(copy_with_target_df$row)))
  cluster_list_idx[length(cluster_list_idx)]<-list(remaining_idx)
  
  return (cluster_list_idx)
}

data_aggregation_new <-function (copy_with_target_df, k)
{
  print("data microaggregation_new")
  
  cluster_list<-c()
  cluster_list_idx<-c()
  
  #print(copy_with_target_df)
  
  
  mean_rec<-mean(copy_with_target_df$dist)
  
  #print(mean_rec)
  
  while(nrow(copy_with_target_df)> k-1)
  {
    
    ci<-c()
    ci_val<-c()
    tmp_df<-data.frame()
    
    colnames(copy_with_target_df)<-c("row","dist","target","diff")
    
    
    diff_df<-(abs(mean_rec-copy_with_target_df[2]))
    copy_with_target_df['diff'] = diff_df
    
    
    most_dist_val<-max(copy_with_target_df$diff)
    most_dist_indx<-match(most_dist_val,copy_with_target_df$diff)
    
    fin_idx<-as.numeric(as.character(copy_with_target_df[most_dist_indx,]$row))
    
    tmp_df<-rbind(tmp_df,copy_with_target_df[most_dist_indx,c(2,3)])
    
    ci<-append(ci,fin_idx)
    ci_val<-append(ci_val,most_dist_val)
    
    copy_with_target_df <- copy_with_target_df[-most_dist_indx,]
    
    
    while (length(ci)<k)
    {
      
      most_dist_val<-max(copy_with_target_df$diff)
      most_dist_indx<-match(most_dist_val,copy_with_target_df$diff)
      
      fin_idx<-as.numeric(as.character(copy_with_target_df[most_dist_indx,]$row))
      
      tmp_df<-rbind(tmp_df,copy_with_target_df[most_dist_indx,c(2,3)])
      
      ci<-append(ci,fin_idx)
      ci_val<-append(ci_val,most_dist_val)
      
      copy_with_target_df <- copy_with_target_df[-most_dist_indx,]
      
      
    }
    
    
    cluster_list<-append(cluster_list,list(ci_val))
    cluster_list_idx<-append(cluster_list_idx,list(ci))
    
  }
  
  #assign remaining values
  remaining_val<-append(cluster_list[length(cluster_list)][[1]],copy_with_target_df$diff)
  cluster_list[length(cluster_list)]<-list(remaining_val)
  
  remaining_idx<-append(cluster_list_idx[length(cluster_list_idx)][[1]],as.numeric(as.character(copy_with_target_df$row)))
  cluster_list_idx[length(cluster_list_idx)]<-list(remaining_idx)
  
  return (cluster_list_idx)
}

data_partition_supervized <-function (copy_with_target_df, k)
{
  
  #############Supervized partioning ##############
  sup_partitions=split(copy_with_target_df, copy_with_target_df$target)
  
  
  cluster_list_idx_tmp<-list()
  
  
  c=0
  for (part in 1:length(sup_partitions))
  {
    cat("part No : ",c,"\n")
    c=c+1
    copy_with_target_df_tmp=data.frame(sup_partitions[part])
    
    if (nrow(copy_with_target_df_tmp)<k)
    {
      print("Not enough items in dataframe")
      break;
    }
    
    else
    {
      cluster_list_idx_part<-data_aggregation_new(copy_with_target_df_tmp,k)
      cluster_list_idx_tmp<-c(cluster_list_idx_tmp,cluster_list_idx_part)
      
      
    }
    
    
  }
  
  cluster_list_idx<-cluster_list_idx_tmp
  
  print("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&")
  print(length(cluster_list_idx))
  
  return (cluster_list_idx)
  
}

proximity_based_reidentification <- function(dataFile_m,dataFile_o,k)
{ 
  #set.seed(100)
  # random_records_1<-1000
  # random_records_2<-ceiling(nrow(dataFile_o)*0.5)
  # 
  # if(random_records_1>random_records_2)
  # {
  #   random_records<-random_records_2
  #   
  # }else
  # {
  #   random_records<-random_records_1
  # }
  # 
  # dataFile_o<-data.frame(dataFile_o[sample(nrow(dataFile_o), random_records), ])
  
  tot_rec<-nrow(dataFile_m)
  
  
  #Measure DR without sensitive attribute and nonQIDs
  df_m <<- dataFile_m[-(length(dataFile_m))]
  df_o <<- dataFile_o[-(length(dataFile_o))]
  
  AD_single <<- c()
  AD_multiple <<- c()
  nn<-k
  
  SA<-names(dataFile_o[ncol(dataFile_o)])
  
  #measure distance
  for (i in 1:nrow(dataFile_o))
  {
    test_df<-data.frame()
    test_df<-rbind(test_df,df_o[i,])
    test_df<-rbind(test_df,df_m)
    rownames(test_df) <- NULL
    
    dist_g<-gower.dist(data.x=test_df[1,] , data.y=test_df[-1,])
    min_dist_idx <- which.min(dist_g[1,])
    
    
    #Single instance
    if (dataFile_m[min_dist_idx,SA]==dataFile_o[i,SA])
    {
      AD_single<-append(AD_single,1)
    }else
    {
      AD_single<-append(AD_single,0)
    }
    
    #Neighbourhood
    min_dist_idx <- which(dist_g[1,] %in% sort(dist_g[1,])[1:nn])
    inferred_SA<-dataFile_m[min_dist_idx,SA]
    inferred_SA<-names(table(inferred_SA))[1]
    
    if (inferred_SA==dataFile_o[i,SA])
    {
      AD_multiple<-append(AD_multiple,1)
    }else
    {
      AD_multiple<-append(AD_multiple,0)
    }
  }
  
  single_AD<-sum(AD_single)/tot_rec
  multiple_AD<-sum(AD_multiple)/tot_rec
  
  #return  (c(single_AD,multiple_AD))
  return  (single_AD)
  
  
} 


proximity_based_reidentification_qid <- function(dataFile_m,dataFile_o,k,qids,istest)
{ 
  print("proximity_based_reidentification_qid")
  
  # random_records_1<-1000
  # random_records_2<-ceiling(nrow(dataFile_o)*0.25)
  # 
  # if(random_records_1>random_records_2)
  # {
  #   random_records<-random_records_2
  #   
  # }else
  # {
  #   random_records<-random_records_1
  # }
  # 
  #dataFile_o<-data.frame(dataFile_o[sample(nrow(dataFile_o), random_records), ])
  
  ######## Measure DR  - fully informed adversary   ######## 
  
  if (istest==1)
  {
    print("Reidentification for test set")
    
    t_size<-nrow(dataFile_m)
    dataFile_o<-dataFile_o[1:t_size,]
    
    
  }
  
  
  tot_rec<-nrow(dataFile_m)
  
  df_m <- dataFile_m[-(length(dataFile_m))]
  df_o <- dataFile_o[-(length(dataFile_o))]
  
  print(qids)
  print(head(df_m))
  print(head(df_o))
  
  AD_single <- c()
  nn<-k
  
  SA<-names(dataFile_o[ncol(dataFile_o)])
  print(SA)
  
  
  #measure distance
  for (i in 1:nrow(dataFile_o))
  {
    test_df<-data.frame()
    test_df<-rbind(test_df,df_o[i,])
    test_df<-rbind(test_df,df_m)
    rownames(test_df) <- NULL
    
    dist_g<-gower.dist(data.x=test_df[1,] , data.y=test_df[-1,])
    min_dist_idx <- which.min(dist_g[1,])
    
    
    #Single instance
    if (dataFile_m[min_dist_idx,SA]==dataFile_o[i,SA])
    {
      AD_single<-append(AD_single,1)
    }else
    {
      AD_single<-append(AD_single,0)
    }
    
  }
  
  print("End FIA")
  
  all_col_AD<-sum(AD_single)/tot_rec
  
  
  ######## Measure DR - partially informed adversary   ######## 
  
  df_m <- dataFile_m[-(length(dataFile_m))]
  df_m <- df_m[,qids]
  
  df_o <- dataFile_o[-(length(dataFile_o))]
  df_o <- df_o[,qids]
  
  AD_single <- c()
  nn<-k
  
  SA<-names(dataFile_o[ncol(dataFile_o)])
  
  #measure distance
  for (i in 1:nrow(dataFile_o))
  {
    test_df<-data.frame()
    test_df<-rbind(test_df,df_o[i,])
    test_df<-rbind(test_df,df_m)
    rownames(test_df) <- NULL
    
    dist_g<-gower.dist(data.x=test_df[1,] , data.y=test_df[-1,])
    min_dist_idx <- which.min(dist_g[1,])
    
    
    #Single instance
    if (dataFile_m[min_dist_idx,SA]==dataFile_o[i,SA])
    {
      AD_single<-append(AD_single,1)
    }else
    {
      AD_single<-append(AD_single,0)
    }
    
  }
  
  
  
  qid_col_AD<-sum(AD_single)/tot_rec
  
  print("End PIA")
  
  
  return  (c(all_col_AD,qid_col_AD))
  
  
} 

F1_Score_micro <- function(y_true, y_pred, labels = NULL) 
{
  if (is.null(labels) == TRUE) labels <- unique(c(y_true, y_pred)) # possible problems if labels are missing from y_*
  Precision <- Precision_micro(y_true, y_pred, labels)
  Recall <- Recall_micro(y_true, y_pred, labels)
  F1_Score_micro <- 2 * (Precision * Recall) / (Precision + Recall)
  return(F1_Score_micro)
}

Precision_micro <- function(y_true, y_pred, labels = NULL) {
  Confusion_DF <- ConfusionDF(y_pred, y_true)
  
  if (is.null(labels) == TRUE) labels <- unique(c(y_true, y_pred))
  # this is not bulletproof since there might be labels missing (in strange cases)
  # in strange cases where they existed in training set but are missing from test ground truth and predictions.
  
  TP <- c()
  FP <- c()
  for (i in c(1:length(labels))) {
    positive <- labels[i]
    
    # it may happen that a label is never predicted (missing from y_pred) but exists in y_true
    # in this case ConfusionDF will not have these lines and thus the simplified code crashes
    # TP[i] <- as.integer(Confusion_DF[which(Confusion_DF$y_true==positive & Confusion_DF$y_pred==positive), "Freq"])
    # FP[i] <- as.integer(sum(Confusion_DF[which(Confusion_DF$y_true!=positive & Confusion_DF$y_pred==positive), "Freq"]))
    
    # workaround:
    # i don't want to change ConfusionDF since i don't know if the current behaviour is a feature or a bug.
    tmp <- Confusion_DF[which(Confusion_DF$y_true==positive & Confusion_DF$y_pred==positive), "Freq"]
    TP[i] <- if (length(tmp)==0) 0 else as.integer(tmp)
    
    tmp <- Confusion_DF[which(Confusion_DF$y_true!=positive & Confusion_DF$y_pred==positive), "Freq"]
    FP[i] <- if (length(tmp)==0) 0 else as.integer(sum(tmp))
  }
  Precision_micro <- sum(TP) / (sum(TP) + sum(FP))
  return(Precision_micro)
}


Recall_micro <- function(y_true, y_pred, labels = NULL) {
  Confusion_DF <- ConfusionDF(y_pred, y_true)
  
  if (is.null(labels) == TRUE) labels <- unique(c(y_true, y_pred))
  # this is not bulletproof since there might be labels missing (in strange cases)
  # in strange cases where they existed in training set but are missing from test ground truth and predictions.
  
  TP <- c()
  FN <- c()
  for (i in c(1:length(labels))) {
    positive <- labels[i]
    
    # short version, comment out due to bug or feature of Confusion_DF
    # TP[i] <- as.integer(Confusion_DF[which(Confusion_DF$y_true==positive & Confusion_DF$y_pred==positive), "Freq"])
    # FP[i] <- as.integer(sum(Confusion_DF[which(Confusion_DF$y_true==positive & Confusion_DF$y_pred!=positive), "Freq"]))
    
    # workaround:
    tmp <- Confusion_DF[which(Confusion_DF$y_true==positive & Confusion_DF$y_pred==positive), "Freq"]
    TP[i] <- if (length(tmp)==0) 0 else as.integer(tmp)
    
    tmp <- Confusion_DF[which(Confusion_DF$y_true==positive & Confusion_DF$y_pred!=positive), "Freq"]
    FN[i] <- if (length(tmp)==0) 0 else as.integer(sum(tmp))
  }
  Recall_micro <- sum(TP) / (sum(TP) + sum(FN))
  return(Recall_micro)
}

ConfusionDF <- function(y_pred, y_true) 
{
  Confusion_DF <- transform(as.data.frame(ConfusionMatrix(y_pred, y_true)),
                            y_true = as.character(y_true),
                            y_pred = as.character(y_pred),
                            Freq = as.integer(Freq))
  return(Confusion_DF)
}

ConfusionMatrix <- function(y_pred, y_true) {
  Confusion_Mat <- table(y_true, y_pred)
  return(Confusion_Mat)
}

ML_based_inference<-function(dataFile_m,dataFile_o)
{
  #dataFile_m <-df_test
  #dataFile_o <- df1
  
  print ("ML_based_inference")
  
  lab <- paste('V', c(1:ncol(dataFile_m)), sep = '')
  colnames(dataFile_m) <- lab
  colnames(dataFile_o) <- lab
  
  #dataFile_m<-na.omit(dataFile_m)
  #dataFile_o<-na.omit(dataFile_o)
  
  
  
  #class_var_str<-names(dataFile_o[ncol(dataFile_o)])
  
  #class_var<-names(dataFile_o[ncol(dataFile_o)])
  #class_var<-as.symbol(class_var)
  
  colnames(dataFile_m)[ncol(dataFile_m)] <- "outcome"
  colnames(dataFile_o)[ncol(dataFile_o)] <- "outcome"
  
  dataFile_m$outcome <- as.factor(dataFile_m$outcome)
  dataFile_o$outcome <- as.factor(dataFile_o$outcome)
  
  
  
  
  for (i in 1:(ncol(dataFile_o)-1))
  {
    
    if (var_list[i]=="N")
    {
      dataFile_o[i] <- data.frame(scale( data.frame(as.numeric(dataFile_o[[i]]))   ))
      dataFile_m[i] <- data.frame(scale( data.frame(as.numeric(dataFile_m[[i]]))   ))
    }
    
  }
  
  
  
  control <- trainControl(method="cv", number=20)
  metric <- "Accuracy"
  fit.cart <- caret::train(outcome ~ ., data=dataFile_m, method="rpart",metric=metric, trControl=control)
  #fit.cart <- randomForest(outcome ~ ., data=dataFile_m, importance=TRUE,proximity=TRUE)
  
  #fit.cart <- ctree(outcome ~ ., data = dataFile_m)
  
  
  print("train")
  
  
  
  pred1 <- predict(fit.cart, dataFile_o)
  CM1 <-table(pred1,dataFile_o[,ncol(dataFile_o)])
  accuracy_test <- (sum(diag(CM1)))/sum(CM1)
  
  
  
  micro.f1 <- F1_Score_micro(data.frame(pred1)[[1]], dataFile_o[,ncol(dataFile_o)], labels = unique(data.frame(pred1)[[1]]))
  
  #print("End")
  
  return(micro.f1)
  
}

ML_QID_based_inference<-function(dataFile_m,dataFile_o,qids)
{
  print("ML_QID_based_inference")
  
  lab <- paste('V', c(1:ncol(dataFile_m)), sep = '')
  colnames(dataFile_m) <- lab
  colnames(dataFile_o) <- lab
  
  qids <- paste('V', qids, sep = '')
  
  
  class_var_str<-names(dataFile_o[ncol(dataFile_o)])
  
  if (class_var_str %in% qids)
  {
    print("SA is QID")
    qids<-mixedsort(qids)
    dataFile_m<-dataFile_m[,qids]
    #print(head(dataFile_m))
    
    dataFile_o<-dataFile_o[,qids]
    #print(head(dataFile_o))
    
    
  }else{
    
    print("SA is not QID")
    class_var<-dataFile_m[ncol(dataFile_m)]
    d_m<-dataFile_m[,qids]
    dataFile_m<-cbind(d_m,class_var)
    print(head(dataFile_m))
    
    class_var<-dataFile_o[ncol(dataFile_o)]
    d_o<-dataFile_o[,qids]
    dataFile_o<-cbind(d_o,class_var)
    print(head(dataFile_o))    
    
  }
  
  
  
  
  #class_var<-as.symbol(class_var)
  colnames(dataFile_m)[ncol(dataFile_m)] <- "class"
  colnames(dataFile_o)[ncol(dataFile_o)] <- "class"
  
  dataFile_m$class <- as.factor(dataFile_m$class)
  dataFile_o$class <- as.factor(dataFile_o$class)
  
  if (masked_df!="ar")
  {
    
    tree1 <- randomForest(class ~. ,data=dataFile_m,ntree=50, na.action=na.omit,importance = TRUE, proximity = TRUE)
    
    pred1 <- predict(tree1,newdata=dataFile_o)
    
    CM1 <-table(pred1,dataFile_o[,ncol(dataFile_o)])
    accuracy_train <- (sum(diag(CM1)))/sum(CM1)
    
    
  }else
  {
    #qid_var_list<-gsub("[^0-9.]", "",  qids)
    #var_list_qid<-var_list[as.numeric(qid_var_list)]
    
    # for (i in 1:(ncol(dataFile_o)-1))
    # {
    #   
    #   if (var_list_qid[i]=="N")
    #   {
    #     dataFile_o[i] <- data.frame(scale( data.frame(as.numeric(dataFile_o[[i]]))   ))
    #     dataFile_m[i] <- data.frame(scale( data.frame(as.numeric(dataFile_m[[i]]))   ))
    #   }
    #   
    # }
    # 
    
    
    control <- trainControl(method="cv", number=20)
    metric <- "Accuracy"
    fit.cart <- caret::train(class ~ ., data=dataFile_m, method="rpart",metric=metric, trControl=control)
    
    pred1 <- predict(fit.cart, dataFile_o)
    CM1 <-table(pred1,dataFile_o[,ncol(dataFile_o)])
    accuracy_test <- (sum(diag(CM1)))/sum(CM1)
    
    
  }
  
  micro.f1 <- F1_Score_micro(data.frame(pred1)[[1]], dataFile_o[,ncol(dataFile_o)], labels = unique(data.frame(pred1)[[1]]))
  
  #print(accuracy_test)
  print("end ML")
  
  return(micro.f1)
  
}

propensity_score<-function(dataFile_m,dataFile_o)
{
  class_var_str<-names(dataFile_o[ncol(dataFile_o)])
  
  class_var<-names(dataFile_o[ncol(dataFile_o)])
  class_var<-as.symbol(class_var)
  
  #colnames(dataFile_m)[ncol(dataFile_m)] <- "class"
  #colnames(dataFile_o)[ncol(dataFile_o)] <- "class"
  
  #Measure DR without sensitive attribute
  df_m <<- dataFile_m[-(length(dataFile_m))]
  df_o <<- dataFile_o[-(length(dataFile_o))]
  
  #add indicator variable
  ind_ori<-rep(c(0), times = nrow(dataFile_o))
  ind_mask<-rep(c(1), times = nrow(dataFile_o))
  
  df_o$group <- unlist(ind_ori)
  df_m$group <- unlist(ind_mask)
  
  #stack dataframe
  stack_df <- rbind(df_m, df_o)
  #print(head(stack_df))
  
  #model
  m_ps <- glm(group~., family = binomial(), data = stack_df)
  
  #pscore
  prs_df <- data.frame(pr_score = predict(m_ps, type = "response"),
                       masked = m_ps$model$group)
  print((prs_df$pr_score ))
  
  logitps <-  -log(1/prs_df$pr_score-1) 
  
  #matchit
  m.out <- matchit(group~., data=stack_df,method= "nearest", ratio=1, 
                   distance= logitps, caliper=0.05, replace= F)
  
  
  #mod_match <- matchit(group~., stack_df[-ncol(stack_df)], method = "nearest", model="logit")
  
  #matchit(group~. , method = "nearest")
  
  #matched count
  dta_m <- match.data(mod_match)
  print(head(dta_m))
}

identity_discloure <- function(dataFile_m,dataFile_o,qids)
{
  print("identity_discloure")
  
  klab <- paste('V', c(colnames(dataFile_o)), sep = '')
  colnames(dataFile_o)<-klab
  colnames(dataFile_m)<-klab
  
  qidlab <- paste('V', c(qids), sep = '')
  
  #### PIA #####
  
  #blocking_var<-sample(qidlab, 1)
  blocking_var<-sample(qidlab, 1)
  
  linked_data_set <- pair_blocking(dataFile_o, dataFile_o, blocking_var) %>%
    compare_pairs(by = qidlab) %>%
    score_problink(var = "weight") %>%
    select_n_to_m("weight", var = "ntom", threshold = 0) %>%
    link()
  
  
  cpy_linked_data_set<-linked_data_set
  
  final_linked<-cpy_linked_data_set[complete.cases(cpy_linked_data_set), ]
  
  linked_ratio_PIA<- nrow(final_linked)/nrow(linked_data_set)
  
  print(linked_ratio_PIA)
  
  
  #### FIA #####
  
  #blocking_var<-sample(qidlab, 1)
  
  blocking_var<-klab[length(klab)]
  
  qidlab<-klab[1:(length(klab)-1)]
  
  linked_data_set <- pair_blocking(dataFile_o, dataFile_m, blocking_var) %>%
    compare_pairs(by = qidlab) %>%
    score_problink(var = "weight") %>%
    select_n_to_m("weight", var = "ntom", threshold = 0) %>%
    link()
  
  
  cpy_linked_data_set<-linked_data_set
  
  final_linked<-cpy_linked_data_set[complete.cases(cpy_linked_data_set), ]
  
  linked_ratio_FIA<- nrow(final_linked)/nrow(linked_data_set)
  
  print(linked_ratio_FIA)
  
  
  return(list(linked_ratio_PIA,linked_ratio_FIA))
  
  
}

probabilistic_anonymity<-function (df, df_test, N_var, C_var, B_var, var_list)
{
  df<-df
  data_for_swap <- df
  data_full <- df
  
  
  data_file_list<-list(dfname,".csv","test.csv")
  f_list_names<-list("Original Data","Test")
  
  AD_risk_single<-list()
  AD_risk_multiple<-list()
  
  AD_Advantage<-list()
  AD_Advantage_ML<-list()
  
  MI_loss_vec<-list(0,0)
  
  ML_accuracy<-list()
  ML_accuracy_qid<-list()
  ID_risk_tot<-list()
  mi_masked<-list()
  qid_quo<-list("-","-")
  numqids<-list(0,0)
  k_val_list<-list("-","-")
  grouped_lst<-list("-","-")
  u_sig_list<-list("-","-")
  
  AD_risk_FIA<-list()
  AD_risk_PIA<-list()
  
  ML_accuracy_FIA<-list()
  ML_accuracy_PIA<-list()
  
  ID_risk_FIA<-list()
  ID_risk_PIA<-list()
  
  
  
  #seperate class variable / sensitive attribute
  class_var <- data_for_swap[length(data_for_swap)]
  data_for_swap<- data_for_swap[-(length(data_for_swap))]
  
  #rename column names
  colnames(data_for_swap)  <- seq(1, length(data_for_swap), by=1)
  
  div_clust_data<-cbind(data_for_swap,class_var)
  colnames(div_clust_data)  <- seq(1, length(div_clust_data), by=1)
  
  
  #Finalize data types 
  if (length(N_var)==0)
  {
    N_var=NULL
  }else if(length(C_var)==0)
  {
    C_var=NULL
  }else if (length(B_var)==0)
  {
    B_var=NULL
  }
  
  
  #generate distance matrix
  
  gower_dist_matrix<-distmix(data_for_swap, method = "gower", idnum = N_var, idbin = B_var, idcat = C_var)
  print(gower_dist_matrix)
  
  ahmad_dist_matrix<-distmix(data_for_swap, method = "ahmad", idnum = N_var, idbin = B_var, idcat = C_var)
  
  data_for_swap_m<-data_for_swap
  
  # for (v in N_var)
  # {
  #   res <- data.frame(discretize(data_for_swap_m[[v]], cuts = 100))
  #   uv <- (unique(res[[1]]))
  #   nv <- c(seq(1:length(uv)))
  #   data_for_swap_m[,v]<-res
  #   data_for_swap_m[,v] <- mapvalues(data_for_swap_m[,v], from=uv, to=nv)
  #   data_for_swap_m[,v]  <- as.numeric(data_for_swap_m[,v])
  # 
  # }
  # 
  
  ahmad_dist_matrix<-distmix(data_for_swap_m, method = "ahmad", idnum = N_var, idbin = B_var, idcat = C_var)
  print(ahmad_dist_matrix)
  
  #construct 1d distances
  gower_dist_matrix_1d<-data.frame(gower_dist_matrix[1,])
  gower_dist_matrix_1d<-data.frame(row.names(gower_dist_matrix_1d),gower_dist_matrix_1d,class_var)
  gower_dist_matrix_1d['diff'] = 0
  colnames(gower_dist_matrix_1d)<-c("row","dist","target","diff")
  print(head(gower_dist_matrix_1d))
  
  # ahmad_dist_matrix_1d<-data.frame(ahmad_dist_matrix)
  # ahmad_dist_matrix_1d<-data.frame(row.names(ahmad_dist_matrix_1d),ahmad_dist_matrix_1d,class_var)
  # ahmad_dist_matrix_1d['diff'] = 0
  # colnames(ahmad_dist_matrix_1d)<-c("row","dist","target","diff")
  
  
  ahmad_dist_matrix_1d<-data.frame(ahmad_dist_matrix)
  
  nc<-nrow(ahmad_dist_matrix)
  
  diff<-rep(0,nrow(ahmad_dist_matrix))
  
  ahmad_dist_matrix_1d<-data.frame(row.names(ahmad_dist_matrix_1d),
                                   class_var,
                                   data.frame(diff),
                                   ahmad_dist_matrix_1d)
  
  colnames(ahmad_dist_matrix_1d)<-c("row","target","diff")
  
  #copy_with_target_df<-ahmad_dist_matrix_1d
  
  
  
  
  #start anonymization
  first_run<-TRUE
  
  #for different qid specifications
  for (q in qid_type)
  {
    
    #min cluster size
    for (k in MA_list)
    { 
      cat("K-val : ",k,"\n")
      
      #qid selection
      if (q=='specified') #use speciifed qids
      {
        qids<-QID_list
        q_str<-"SP"
        
      }else if (q=='all') #consider all as qids
      {
        qids<-colnames(data_for_swap)
        q_str<-"ALL"
        
      }else if (q=='significant') #consider all as qids
      {
        qids<-Var_significance(data_for_swap,class_var)
        qids<-unlist(qids)
        q_str<-"SIG"
      }
      
      if (first_run==TRUE)
      {
        
        #####################################################
        #     Masked data membership/identity disclosure  #
        #####################################################
        
        # ID_risk_res<-identity_discloure(df,df,qids)
        # ID_risk_PIA<-append(ID_risk_PIA,(ID_risk_res[[1]]) )
        # ID_risk_FIA<-append(ID_risk_FIA,(ID_risk_res[[2]]) )
        # 
        #####################################################
        #     Original data adversarial Attribute disclosure  #
        ##################################################### 
        
        
        #proximity based AD
        AD_risk_res  <- proximity_based_reidentification_qid(df,df,k=1,qids,0)
        
        AD_risk_FIA  <- append(AD_risk_FIA,list(AD_risk_res[1]))
        AD_risk_PIA  <- append(AD_risk_PIA,list(AD_risk_res[2]))
        
        
        #ML based AD
        #acc<-ML_based_inference(df,df)
        acc<-0
        
        ML_accuracy_FIA<-append(ML_accuracy_FIA,acc)
        
        
        acc<-ML_QID_based_inference(df,df,qids)
        ML_accuracy_PIA<-append(ML_accuracy_PIA,acc)
        
        
        #####################################################
        #     Test data membership/identity disclosure  #
        #####################################################
        
        # ID_risk_res<-identity_discloure(df_test,df,qids)
        # ID_risk_PIA<-append(ID_risk_PIA,c(ID_risk_res[[1]]) )
        # ID_risk_FIA<-append(ID_risk_FIA,c(ID_risk_res[[2]]) )
        # 
        
        
        
        #####################################################
        #     Test data adversarial Attribute disclosure  #
        ##################################################### 
        
        print ("Test data")
        
        
        #proximity based AD
        AD_risk_res  <- proximity_based_reidentification_qid(df_test,df,k=1,qids,1)
        
        AD_risk_FIA  <- append(AD_risk_FIA,list(AD_risk_res[1]))
        AD_risk_PIA  <- append(AD_risk_PIA,list(AD_risk_res[2]))
        
        #ML based AD
        acc<-0#ML_based_inference(df_test,df)
        ML_accuracy_FIA<-append(ML_accuracy_FIA,acc)
        
        acc<-ML_QID_based_inference(df_test,df,qids)
        ML_accuracy_PIA<-append(ML_accuracy_PIA,acc)
        
        first_run<-FALSE
        
      } 
      
      ########## clustering data ##################
      
      ######## to 1d distances and microaggregation for clustering #######
      
      #magg_cluster_list_idx_g<-data_aggregation_new(gower_dist_matrix_1d,k)
      
      magg_cluster_list_idx_g<-data_partition_supervized(gower_dist_matrix_1d,k)
      print(magg_cluster_list_idx_g)
      clust_state<- min(unlist(lapply(magg_cluster_list_idx_g, length)))>=k
      if (clust_state!=TRUE)
      {
        stop("Min cluster size not reached, MA Gower!")
      }
      
      c_size_g_m <<- c(c_size_g_m, mean((unlist(lapply(magg_cluster_list_idx_g, length)))))
      
      #c_size_g_m <<- append(c_size_g_m, list(unlist(lapply(magg_cluster_list_idx_g, length))))
      
      
      #magg_cluster_list_idx_a<-data_aggregation_new(ahmad_dist_matrix_1d,k)
      
      magg_cluster_list_idx_a <- data_partition_supervized(ahmad_dist_matrix_1d,k)
      
      clust_state<- min(unlist(lapply(magg_cluster_list_idx_a, length)))>=k
      if (clust_state!=TRUE)
      {
        stop("Min cluster size not reached, MA Ahmad!")
      }
      
      c_size_a_m <<- c(c_size_a_m, mean((unlist(lapply(magg_cluster_list_idx_a, length)))))
      
      #c_size_a_m <<- append(c_size_a_m, list(unlist(lapply(magg_cluster_list_idx_a, length))))
      
      
      ####### distance matrix and used constrained clustering #######
      
      dist_g<-distances(gower_dist_matrix)
      
      dist_a<-distances(ahmad_dist_matrix)
      
      print("Convert to distances done!")
      
      #g_clustering <- hierarchical_clustering(dist_g, k)
      #a_clustering <- hierarchical_clustering(dist_a, k)
      
      
      #cluster with minimum size
      
      ################### Gower ###################################
      g_clustering <- sc_clustering(dist_g, k)
      
      #print(get_clustering_stats(dist_g, g_clustering))
      
      
      c_size_g_h <<- c(c_size_g_h,  get_clustering_stats(dist_g, g_clustering)$avg_cluster_size)
      
      
      # g_clustering <- hierarchical_clustering(dist_g,
      #                                         size_constraint = k,
      #                                         existing_clustering = g_clustering)
      # 
      clust_state<-check_clustering(g_clustering, k)
      if (clust_state!=TRUE)
      {
        stop("Min cluster size not achieved PKNN-Gower!")
        
      }
      
      g_clustering <- data.frame(g_clustering)
      
      #c_size_g_h <<- append(c_size_g_h,  list(data.frame(table(data.frame(g_clustering)$cluster_label))$Freq))
      
      #get_clustering_stats(dist_g, g_clustering)
      
      print("Gower done!")
      
      ################### Ahmad-Dey ###################################
      
      
      
      #a_clustering <- hierarchical_clustering(dist_a, k)
      
      a_clustering <- sc_clustering(dist_a, k)
      
      
      #print(get_clustering_stats(dist_a, a_clustering))
      
      c_size_a_h <<- c(c_size_a_h, get_clustering_stats(dist_a, a_clustering)$avg_cluster_size)
      
      
      # a_clustering <- hierarchical_clustering(dist_a,
      #                                           size_constraint = k,
      #                                           existing_clustering = a_clustering)
      
      clust_state<-check_clustering(a_clustering, k)
      if (clust_state!=TRUE)
      {
        stop("Min cluster size not achieved PKNN-Ahmad-Dey!")
        
      }
      
      a_clustering <- data.frame(a_clustering)
      
      
      #c_size_a_h <<- append(c_size_a_h,  list(data.frame(table(data.frame(a_clustering)$cluster_label))$Freq))
      
      
      print("Ahmd-Dey done!")
      
      ################################################################
      
      u_vals <- unique(g_clustering$cluster_label )
      hclust_g_index_list <- list()
      
      for (u in u_vals)
      {
        hclust_g_index_list <-append(hclust_g_index_list, list(g_clustering[g_clustering$cluster_label == u,]$id))
        
      }
      
      
      u_vals <- unique(a_clustering$cluster_label )
      hclust_a_index_list <- list()
      
      for (u in u_vals)
      {
        hclust_a_index_list <-append(hclust_a_index_list, list(a_clustering[a_clustering$cluster_label == u,]$id))
        
      } 
      
      #different distance and clustering 
      index_lists<-c(list(magg_cluster_list_idx_g),
                     list(magg_cluster_list_idx_a)
      )
      
      
      # index_lists<-c(list(hclust_g_index_list), 
      #                list(hclust_a_index_list))
      # 
      #permutation 
      for (group in group_list)
      {
        
        
        
        if (group==0)
        {
          grouped<-"NoAB"
        }else
        {
          grouped<-"WithAB"
        }              
        
        
        id=1             
        for (ind in index_lists)
        {
          
          
          
          numqids<-append(numqids,length(qids))
          k_val_list<-append(k_val_list,k)
          grouped_lst<-append(grouped_lst,group)
          
          
          
          if (id==1)
          {
            clust_dist<-"MAGG_GRWR"
            
          }else if (id==2)
          {
            clust_dist<-"MAGG_AHMD"
          }else if (id==3)
          {
            clust_dist<-"HCLUST_GRWR"
          }else if (id==4)
          {
            clust_dist<-"HCLUST_AHMD"
          }                        
          
          id=id+1
          
          cat("Grouped : ", group, " clustering : ",clust_dist, "\n")
          
          masked_dataframe<-data_permutation_with_Group (data_full, qids, group, ind)
          colnames(masked_dataframe)<-colnames(data_full)
          
          
          fname <- paste0("PKANN_",k,"_","NQID_",(length(qids)),"_",grouped,"_",clust_dist)
          f_list_names<-append(f_list_names,fname)
          
          fname <- paste0(fname,"_",dfname,".csv")
          write.table(masked_dataframe,file = paste0(w_path,fname),row.names = FALSE,col.names=FALSE,sep = ",",quote=FALSE)		  
          data_file_list<-append(data_file_list,fname)
          
          #####################################################
          #     Masked data membership/identity disclosure  #
          #####################################################
          
          # ID_risk_res<-identity_discloure(masked_dataframe,df1,qids)
          # ID_risk_PIA<-append(ID_risk_PIA,c(ID_risk_res[[1]]) )
          # ID_risk_FIA<-append(ID_risk_FIA,c(ID_risk_res[[2]]) )
          # 
          
          #####################################################
          #     Masked data adversarial Attribute disclosure  #
          #####################################################
          
          print ("AD Masked data")
          
          
          AD_risk_res <- proximity_based_reidentification_qid(masked_dataframe,df1,k,qids,0)
          
          AD_risk_FIA  <- append(AD_risk_FIA,list(AD_risk_res[1]))
          AD_risk_PIA  <- append(AD_risk_PIA,list(AD_risk_res[2]))
          
          
          acc<-0#ML_based_inference(masked_dataframe,df1)
          ML_accuracy_FIA<-append(ML_accuracy_FIA,acc)
          
          acc<-ML_QID_based_inference(masked_dataframe,df1,qids)
          ML_accuracy_PIA<-append(ML_accuracy_PIA,acc)          
          
          
          
          #####################################################
          #                        Utility                    #
          #####################################################
          
          
          mi <- Utility_full(df1,masked_dataframe)
          MI_loss_vec<-append(MI_loss_vec,mi)
          
          #MI_info<-mi[2]
          
          
        }
        
      }
      
    }
  }
  
  
  fname <- paste0("Masked_File_List_",dfname,".csv")
  write.table(f_list_names,file=paste0(w_path,fname),row.names = FALSE,col.names=FALSE,sep = ",",quote=FALSE)
  
  
  
  d<-data.frame( unlist(f_list_names),
                 unlist(numqids), 
                 unlist(k_val_list),
                 unlist(grouped_lst),
                 unlist(AD_risk_FIA),
                 unlist(AD_risk_PIA), 
                 unlist(ML_accuracy_FIA), 
                 unlist(ML_accuracy_PIA),
                 unlist(MI_loss_vec))
  print("##########################")
  
  return(d)
}

utility_score_original_data<-function (dataFile_o)
{
  #print("Utility")
  
  #original data
  m<-ncol(df1)-1
  MI_vector_int<-list()
  for (i in 1:ncol(dataFile_o))
  {
    class_df<-dataFile_o[i]
    class_name<-names(class_df)
    feature_df= dataFile_o[ , !(names(dataFile_o) %in% class_name)]
    
    selected_attr<-JMIM(feature_df, class_df[[1]],m)
    
    MI_vector_int<-append(MI_vector_int, mean(unlist(array((data.frame(selected_attr$score))))) )
    
  }
  
  return(mean(unlist(MI_vector_int),na.rm =TRUE))
  
}

utility_score_masked_data<-function (dataFile_m)
{
  #print("Utility")
  #masked data
  m<-ncol(df1)-1
  
  MI_vector_int<-list()
  for (i in 1:ncol(dataFile_m))
  {
    class_df<-dataFile_m[i]
    class_name<-names(class_df)
    feature_df= dataFile_m[ , !(names(dataFile_m) %in% class_name)]
    
    selected_attr<-JMIM(feature_df, class_df[[1]],m)
    
    MI_vector_int<-append(MI_vector_int, mean(unlist(array((data.frame(selected_attr$score))))) )
    
  }
  
  return((unlist(MI_vector_int)))
  
}

Utility<-function(dataFile_o,dataFile_m)
{
  print("Utility")
  
  
  lab <- paste('V', c(1:ncol(dataFile_o)), sep = '')
  colnames(dataFile_m) <- lab
  colnames(dataFile_o) <- lab
  
  
  feature_df_o<-dataFile_o[1:(ncol(dataFile_o)-1)]
  class_df_o<-dataFile_o[ncol(dataFile_o)]
  
  
  feature_df_m<-dataFile_m[1:(ncol(dataFile_m)-1)]
  class_df_m<-dataFile_m[ncol(dataFile_m)]
  
  
  MI_vector_o<-list()
  MI_vector_m<-list()
  
  for (i in 1:ncol(feature_df_o))
  {
    cat("Var : ",i,"\n")
    
    x <- tryCatch(
      {
        MI_val_O <- mutinformation(feature_df_o[[i]],class_df_o)
        
        MI_val_m <- mutinformation(feature_df_m[[i]],class_df_m)
        
      },
      error = function(e){
        
        
        
        print("Microaggregation......")
        
        k<-5
        opt_ma_tmp <- microaggregation(feature_df_o[i], aggr=k)
        opt_ma_tmp <- unname(as.list(opt_ma_tmp$mx))
        opt_ma_tmp <- as.data.frame(opt_ma_tmp)
        colnames(opt_ma_tmp)<-colnames(feature_df_o[i])
        feature_df_o[[i]]<-round(opt_ma_tmp)
        
        
        opt_ma_tmp <- microaggregation(feature_df_m[i], aggr=k)
        opt_ma_tmp <- unname(as.list(opt_ma_tmp$mx))
        opt_ma_tmp <- as.data.frame(opt_ma_tmp)
        colnames(opt_ma_tmp)<-colnames(feature_df_m[i])
        feature_df_m[[i]]<-round(opt_ma_tmp)
        
        
        
        
      }
    )
    
    
    MI_vector_o<-append(MI_vector_o,MI_val_O)
    MI_vector_m<-append(MI_vector_m,MI_val_m)
    
  }
  
  MI_loss<-(mean(unlist(MI_vector_o))-mean(unlist(MI_vector_m)))
  #print(MI_loss)
  return(MI_loss)
}


Utility_full<-function(dataFile_o,dataFile_m)
{
  print("Utility")
  
  
  lab <- paste('V', c(1:ncol(dataFile_o)), sep = '')
  colnames(dataFile_m) <- lab
  colnames(dataFile_o) <- lab
  
  
  
  class_df_o<-dataFile_o[ncol(dataFile_o)]
  
  
  feature_df_m<-dataFile_m[1:(ncol(dataFile_m)-1)]
  class_df_m<-dataFile_m[ncol(dataFile_m)]
  
  
  MI_vector_o<-list()
  MI_vector_m<-list()
  
  for (i in 1:ncol(dataFile_o))
  {
    
    for (j in 1:ncol(dataFile_o))
    {
      
      cat("Var : ",i," ",j,"\n")
      
      x <- tryCatch(
        {
          MI_val_O <- mutinformation(dataFile_o[[i]],dataFile_o[[j]])
          
          MI_val_m <- mutinformation(dataFile_m[[i]],dataFile_m[[j]])
          
        },
        error = function(e){
          
          
          
          print("Microaggregation......")
          
          k<-5
          opt_ma_tmp <- microaggregation(dataFile_o[i], aggr=k)
          opt_ma_tmp <- unname(as.list(opt_ma_tmp$mx))
          opt_ma_tmp <- as.data.frame(opt_ma_tmp)
          colnames(opt_ma_tmp)<-colnames(dataFile_o[i])
          dataFile_o[[i]]<-round(opt_ma_tmp)
          
          
          opt_ma_tmp <- microaggregation(dataFile_m[i], aggr=k)
          opt_ma_tmp <- unname(as.list(opt_ma_tmp$mx))
          opt_ma_tmp <- as.data.frame(opt_ma_tmp)
          colnames(opt_ma_tmp)<-colnames(dataFile_m[i])
          dataFile_m[[i]]<-round(opt_ma_tmp)
          
          
          
          
        }
      )
      
      
      MI_vector_o<-append(MI_vector_o,MI_val_O)
      MI_vector_m<-append(MI_vector_m,MI_val_m)
    }   
  }
  
  MI_loss<-(mean(unlist(MI_vector_o))-mean(unlist(MI_vector_m)))
  #print(MI_loss)
  return(MI_loss)
}

MI_Info<-function(dataFile_o)
{
  print("Utility")
  
  
  lab <- paste('V', c(1:ncol(dataFile_o)), sep = '')
  colnames(dataFile_o) <- lab
  
  
  feature_df_o<-dataFile_o[1:(ncol(dataFile_o)-1)]
  class_df_o<-dataFile_o[ncol(dataFile_o)]
  
  
  MI_vector_o<-list()
  
  for (i in 1:ncol(feature_df_o))
  {
    cat("Var : ",i,"\n")
    
    x <- tryCatch(
      {
        MI_val_O <- mutinformation(feature_df_o[[i]],class_df_o)
        
      },
      error = function(e){
        
        
        
        print("Microaggregation......")
        
        k<-5
        opt_ma_tmp <- microaggregation(feature_df_o[i], aggr=k)
        opt_ma_tmp <- unname(as.list(opt_ma_tmp$mx))
        opt_ma_tmp <- as.data.frame(opt_ma_tmp)
        colnames(opt_ma_tmp)<-colnames(feature_df_o[i])
        feature_df_o[[i]]<-round(opt_ma_tmp)
        
        
      }
    )
    
    
    MI_vector_o<-append(MI_vector_o,MI_val_O)
    
  }
  
  return(unlist(MI_vector_o))
}

QID_selection_on_MI<-function (df1,nqids)
{
  
  
  
  MI_vector<-list()
  selected_attr<-c()
  m<-ncol(df1)-1
  
  if(nqids<1)
  {
    print("Use p value thresholding..")
    
    om<-JMIM(df1[1:m],df1[[ncol(df1)]],m)
    original_MI<-list(data.frame(om$score)$om.score)
    
    #print("Compute MI for permuted data..")
    permuted_MI<-list()
    for (j in 1:p)
    {
      mm<-JMIM(df1[1:m], sample(df1[[ncol(df1)]]),m)
      permuted_MI<-append(permuted_MI,list(data.frame(mm$score)$mm.score))
    }
    
    for (l in 1:length(permuted_MI[[1]]))
    {
      perm_g_t_original<-c()
      
      for (j in 1:length(permuted_MI))
      {
        
        if (original_MI[[1]][l] < permuted_MI[[j]][l])
        {
          perm_g_t_original<-append(perm_g_t_original,1)
        }else
        {
          perm_g_t_original<-append(perm_g_t_original,0)
        }
      }
      
      p_val<-(sum(perm_g_t_original)+1)/(p+1)
      #p_val<-(sum(perm_g_t_original)+1)/(p+1)
      
      #estimate p-val based on binomial confidence interval
      #p_confidence_interval<-binom.confint(sum(perm_g_t_original), p, conf.level = 0.99,methods = "exact")
      #lower_ci<-binom.confint(sum(perm_g_t_original), p, conf.level = 0.99, methods = "exact")[[5]]
      #upper_ci<-binom.confint(sum(perm_g_t_original), p, conf.level = 0.99, methods = "exact")[[6]]
      
      # for 99% CI
      # z_val<-2.58
      # 
      # lower_ci<- alfa-(z_val*sqrt((alfa*(1-alfa))/p))
      # upper_ci<- alfa+(z_val*sqrt((alfa*(1-alfa))/p))
      # 
      # std_error<-sqrt((alfa*(1-alfa))/p)
      # coefficient_of_variation<-std_error/alfa
      
      #if (p_val<=alfa)
      #if p value is wihtin the 99% confidence interval we can reject null hypothesis
      # if (((p_val<=upper_ci) && (p_val>=lower_ci)))
      # {
      #   #reject H0
      #   cat("MI between Variable ",ncol(df1)," and ",l," is not statistically significant ",lower_ci," < ", p_val," <" ,upper_ci, "\n")
      # }else
      # {
      #   cat("MI between Variable ",ncol(df1)," and ",l," is statistically significant \n")
      #   selected_attr<-append(selected_attr,paste0("V",l))
      #   
      # }
      
      if (p_val<=alfa)
      {
        cat("MI between Variable ",ncol(df1)," and ",l," is statistically significant ",p_val,  "\n")
        selected_attr<-append(selected_attr,paste0("V",l))
      }else
      {
        cat("MI between Variable ",ncol(df1)," and ",l," is not statistically significant \n")
      }
      
      
      
    }
    
    MI_vector<-append(MI_vector,list(selected_attr))
    
    
  }else
  {
    print("Use user defined # of qids..")
    om<-JMIM(df1[1:m],df1[[ncol(df1)]],nqids)
    original_MI<-list(data.frame(om$score)$om.score)
    
    MI_vector<-append(MI_vector,list(rownames(data.frame(om$score))) )
  }
  
  print("Selected attribute names : ")
  print(MI_vector)
  return(MI_vector)
}

QID_selection_on_MI2<-function (df1,nqids)
{
  MI_vector<-list()
  selected_attr<-c()
  m<-ncol(df1)-1
  
  if(nqids<1)
  {
    print("Use p value thresholding..")
    
    om<-mutinformation(df1,method= "emp")[ncol(df1),]
    original_MI<-list((array(om)))
    
    #print("Compute MI for permuted data..")
    permuted_MI<-list()
    for (j in 1:p)
    {
      df1_mm<-df1
      df1_mm[[ncol(df1)]]<- sample(df1[[ncol(df1_mm)]])
      mm<-mutinformation(df1_mm,method= "emp")[ncol(df1_mm),]
      permuted_MI<-append(permuted_MI,list(array(mm)))
    }
    
    for (l in 1:length(permuted_MI[[1]]))
    {
      perm_g_t_original<-c()
      
      for (j in 1:length(permuted_MI))
      {
        
        if (original_MI[[1]][l] < permuted_MI[[j]][l])
        {
          perm_g_t_original<-append(perm_g_t_original,1)
        }else
        {
          perm_g_t_original<-append(perm_g_t_original,0)
        }
      }
      
      p_val<-sum(perm_g_t_original)/p
      
      if (p_val<=alfa)
      {
        cat("MI between Variable ",ncol(df1)," and ",l," is statistically significant ",p_val,  "\n")
        selected_attr<-append(selected_attr,paste0("V",l))
      }else
      {
        cat("MI between Variable ",ncol(df1)," and ",l," is not statistically significant \n")
      }
    }
    
    MI_vector<-append(MI_vector,list(selected_attr))
    
    
  }else
  {
    print("Use user defined # of qids..")
    om<-JMIM(df1[1:m],df1[[ncol(df1)]],nqids)
    original_MI<-list(data.frame(om$score)$om.score)
    
    MI_vector<-append(MI_vector,list(rownames(data.frame(om$score))) )
  }
  
  #print(MI_vector)
  return(MI_vector)
}

QID_selection_on_MI3<-function (df1,nqids)
{
  
  cat("QID_selection_on_MI3 :",nqids,  "\n")
  
  #avearge MI
  MI_vector<-list()
  selected_attr<-c()
  m<-ncol(df1)-1
  
  feature_df<-df1[,1:(ncol(df1)-1)]
  class_df<-df1[,(ncol(df1))]
  
  
  if(nqids<1)
  {
    om<-nmiMatrix(df1)
    om<-om[,(ncol(df1))]
    
    MI_t=mean(array(om))
    om[om<MI_t]=0
    
    selected_attr<-om[om!=0]
    
    print(selected_attr)
    
    MI_vector<-names(selected_attr)
  }else if (nqids==(ncol(df1)-1))
  {
    #cat(nqids,(ncol(df1)-1),"\n")
    MI_vector<-names(df1)[1:(ncol(df1)-1)]
    
  } else
  {
    
    om<-nmiMatrix(df1)
    om<-om[,(ncol(df1))]
    
    MI_t=mean(array(om))
    om[om<MI_t]=0
    
    selected_attr<-om[om!=0]
    
    selected_attr<-sort(selected_attr,decreasing = TRUE)
    
    nqids<-length(selected_attr)*0.5
    selected_attr<-selected_attr[1:nqids]
    
    MI_vector<-names(selected_attr)
  }
  
  
  print(MI_vector)
  
  return(MI_vector)
}

Var_significance<-function (df,class)
{
  print("Var_significance")
}

re_identification<-function(df,var_order)
{
  #print("+++++++++++++++++++++++++++++++")
  #cat("var_order : ",var_order,"\n")
  
  reidentification_ratio<-c()
  ROC_list<-c()
  reid_max_reched<-FALSE
  
  if (length(var_order)>1)
  {
    #print("Multiple unique attributes exists")
    for (i in 1:length(var_order))
    {
      attr_idx<-var_order[1:i]
      #print(attr_idx)
      composite_key<-df[attr_idx]
      reids<-nrow(composite_key[!(duplicated(composite_key) | duplicated(composite_key, fromLast = TRUE)), ])/nrow(df)
      #print(reids)
      if (length(reids)==0)
      {
        reids<-0
        reidentification_ratio<-append(reidentification_ratio,reids)
        
        
        
      } else if ((length(reids) != 0) && (reids>cumulative_reid))
      {
        
        reidentification_ratio<-append(reidentification_ratio,reids)
        reid_max_reched<-TRUE
        QIDS=attr_idx
        #cat(attr_idx," : ",reids,"\n")
        #print("Reid max reached!")
        break;
        
      }else if  ((length(reids) != 0) && (reids<cumulative_reid))
      {
        
        reidentification_ratio<-append(reidentification_ratio,reids)
      }
      
      
      #cat(attr_idx," : ",reids,"\n")
      
      
    }
    
    if (reid_max_reched==TRUE)
    {
      QIDS=attr_idx
    }
    else
    {
      #print("Reid max not reached check ReidROC")
      for(j in 2:length(reidentification_ratio))
      {
        ROC=(reidentification_ratio[j]-reidentification_ratio[j-1])
        ROC_list<-append(ROC_list,ROC)
        
      }
      
      QID_limit=which(ROC_list==roc_thesh)
      
      if(length(QID_limit)==0)
      {
        QID_limit=which(abs(ROC_list-roc_thesh)==min(abs(ROC_list-roc_thesh)))      
        QIDS=var_order[1:QID_limit]
        
      }else
      {
        
        QID_limit=QID_limit[1]
        if(length(QID_limit)!=0)
        {
          QIDS=var_order[1:QID_limit]
        }else
        {
          QID_limit=which.max(ROC_list)
          QIDS=var_order[1:QID_limit]
        }
        
      }
      
      
    }
  }
  else if (length(var_order)==1)
  {
    print("Only one unique attributes exists")
    
    attr_idx=var_order[1]
    
    composite_key=df[attr_idx]
    
    reids=nrow(composite_key[!(duplicated(composite_key) | duplicated(composite_key, fromLast = TRUE)), ])/nrow(df)
    
    if (length(reids)==0)
    {
      reids=0
    }
    
    
    reidentification_ratio<-append(reidentification_ratio,reids)
    ROC_list<-c()
    QIDS<-var_order
  }
  
  
  
  res<-list(reidentification_ratio,ROC_list,QIDS)
  
  return(res)
}

re_identification_non_unique<-function(df,var_order)
{
  #cat("var_order nonunique : ",var_order,"\n")
  
  reidentification_ratio<-c()
  ROC_list<-c()
  reid_max_reched<-FALSE
  
  if (length(var_order)>1)
  {
    #print("Multiple unique attributes exists")
    for (i in 1:length(var_order))
    {
      attr_idx=var_order[1:i]
      composite_key=df[attr_idx]
      reids=nrow(composite_key[!(duplicated(composite_key) | duplicated(composite_key, fromLast = TRUE)), ])/nrow(df)
      
      if (length(reids)==0)
      {
        reids<-0
        reidentification_ratio<-append(reidentification_ratio,reids)
        QIDS<-attr_idx   
        
        
      } else 
      {
        reidentification_ratio<-append(reidentification_ratio,reids)
        QIDS<-attr_idx    
        
      }
      
      #cat(attr_idx," : ",reids,"\n")
      
      if (reids>=cumulative_reid)
      {
        reid_max_reched<-TRUE
        #print("Max reidentification ratio reached!")
        break
      }
      
    }
    
  }else if (length(var_order)==1)
  {
    print("Only one attributes exists")
    
    attr_idx=var_order[1]
    
    composite_key=df[attr_idx]
    
    reids=nrow(composite_key[!(duplicated(composite_key) | duplicated(composite_key, fromLast = TRUE)), ])/nrow(df)
    
    if (length(reids)==0)
    {
      reids=0
    }
    
    cat(attr_idx," : ",reids,"\n")
    
    reidentification_ratio<-append(reidentification_ratio,reids)
    QIDS<-attr_idx
  }
  
  
  
  res<-list(reidentification_ratio,ROC_list,QIDS)
  
  return(res)
}

uniqueness_detection<-function(df)
{
  print("uniqueness_detection....")
  
  for (i in 1:ncol(df))
  {
    n_items=nrow(df[i])
    
    if (var_list[i]=="C")
    {
      uniqueness_ratio= sum(table(df[i])<=thresh)/n_items 
      unique_list<-append(unique_list,uniqueness_ratio)
    }
    else
    {
      u_items=length(unlist(unique(df[i])))
      ratio=u_items/n_items
      
      #decretize numerical data
      if (ratio>0.7)
      {
        
        k <<- 5
        opt_ma_tmp <<- microaggregation(df[i], aggr=k)
        opt_ma_tmp <<- unname(as.list(opt_ma_tmp$mx))
        opt_ma_tmp <<- as.data.frame(opt_ma_tmp)
        colnames(opt_ma_tmp)<-colnames(df[i])
        #Reconstruct data file
        df[i]<-opt_ma_tmp
        
      }   
      
      
      uniqueness_ratio= sum(table(df[i])<=thresh)/n_items 
      unique_list<-append(unique_list,uniqueness_ratio)
      
      
    }
    #print( length(unlist(unique(df1[i]))) /n_items )
    
  }
  
  unique_df=data.frame(variable_names,unique_list)
  unique_df=unique_df[order(unique_df$unique_list,decreasing = TRUE),]
  
  
  #from sorted list get no_risk_attributes
  if(sum(unique_df$unique_list)!=0)
  {
    print("Valid unique variables are found")
    
    ################################################
    #               Uniqueness based               #
    ################################################
    #print("Uniqueness based ")
    unique_attr_ratio<<-c()
    for (i in 1:ncol(df))
    {
      uv=nrow(unique(df[i]))/nrow(df)
      unique_attr_ratio<<-append(unique_attr_ratio,uv)
    }
    unique_df<-data.frame(variable_names,unlist(unique_attr_ratio))
    unique_df<-unique_df[order(unique_df$unlist.unique_attr_ratio.,decreasing = TRUE),]
    var_order_unique<-array(unique_df$variable_names)
    
    uniqueness_results <-re_identification(df1,var_order_unique)
    
    
    
  }else
  {
    print("No unique variables are found, rely on correlation to identify QIDs")
    #singleton_results<-rep( list(list()), 3 )
    uniqueness_results<-rep( list(list()), 3 )
    
  }
  cat("Unique QID : ")
  #print(uniqueness_results[[3]])
  return(uniqueness_results[[3]])
}

load_data <- function(df_path,df_list,masked_df,w_path)
{
  print("load data")
  df1 <<- read.csv(paste0(df_path,df_list), header=FALSE,fileEncoding="UTF-8-BOM") 
  df1 <<- df1[complete.cases(df1), ]
  #df1 <<- df1[1:100,]
  
  variable_names<-colnames(df1)
  
  
  bin_val=c(0,1)
  #Data types update
  for (attr in length(colnames(df1))-1 )
  {
    u_val<-unique(df1[[attr]] )
    
    if ( (length(u_val)==2) & (setequal(u_val,bin_val) ) )
    {
      var_list[attr]='B'
      
    }
    
  }
  
  N_var=which(var_list %in% 'N')
  C_var=which(var_list %in% 'C')
  B_var=which(var_list %in% 'B')
  
  
  #split to train and test
  #set aside test data
  df_test <<- df1[sample(nrow(df1), nrow(df1)*0.05), ]
  tfname <<- paste0("test_",masked_df,".csv")
  write.table(df_test,file =paste0(w_path,tfname),row.names = FALSE,col.names=FALSE,sep = ",",quote=FALSE)
  row.names(df_test)<-seq(1, nrow(df_test), by=1)
  
  
  #create  df for training by removing test
  df1<<- df1[-c(as.numeric(row.names(df_test))), ]
  dffname <<- paste0("fin_",masked_df,".csv")
  write.table(df1,file =paste0(w_path,dffname),row.names = FALSE,col.names=FALSE,sep = ",",quote=FALSE)
  row.names(df1)<-seq(1, nrow(df1), by=1)
  
  colnames(df1) <-seq(1, ncol(df1), by=1)
  colnames(df_test)<-seq(1, ncol(df_test), by=1)
  
  
  return(list(df_test,df1,N_var,C_var,B_var))
  
  
  
}

######################################################
#                 Start PKNN                           #
######################################################

for (r in 1:num_rounds)
{
  dir.create(paste0(res_path,masked_df))
  dir.create(paste0(res_path,"/",masked_df,"/","Round_",r))
  w_path <-  paste0(res_path,masked_df,"/","Round_",r,"/")
  
  cat("Start round : ", r, "\n")
  
  #load data
  df_out <- load_data(df_path,df_list,masked_df,w_path)
  df_test <- df_out[[1]]
  df1  <- df_out[[2]]
  N_var <- df_out[[3]]
  C_var <- df_out[[4]]
  B_var <- df_out[[5]]
  
  #####masked data results #####
  AD_risk<-probabilistic_anonymity(df1, df_test, N_var,C_var,B_var,var_list)
  
  #final formatting
  rownames(AD_risk)<-NULL
  colnames(AD_risk)<-c("DataFile","NumQID","k","Grouped","DAD-FIA","DAD-PIA","MLAD-FIA","MLAD-PIA","MILoss")
  print(AD_risk)
  
  
  fname <- paste0(r,"_AD_Risk_",dfname,".csv")
  write.table((AD_risk),file<-paste0(w_path,fname),row.names = FALSE,col.names=TRUE,sep = ",",quote=FALSE)
  cat("Round : ", r, " end \n")
}
cat("c_size_g_h")
print(unlist(c_size_g_h))

cat("c_size_a_h")
print(unlist(c_size_a_h))

cat("c_size_a_m")
print(unlist(c_size_a_m))

cat("c_size_g_m")
print(unlist(c_size_g_m))
