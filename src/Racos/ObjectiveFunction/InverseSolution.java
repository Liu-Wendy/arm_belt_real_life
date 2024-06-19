package Racos.ObjectiveFunction;

public class InverseSolution {

    double PI;
    double D1;
    double A1;
    double A2;
    double A3;
    double D4;
    double L;
    double[] tool_offset ;
    int NOSOLUTION;
    double v_max;
    double[] theta_speed_max;
    double[] theta_speed;
    double[] a_max_fast;
    double[] w_fast;
    double[] a_fast;
    double a_max_forward;
    double[] v_forward;
    double[] a_forward;
    double[] v_doorlike;
    public InverseSolution(){
        PI=3.1415926;
        D1=127.000;
        A1=29.690;
        A2=108.000;
        A3=20.000;
        D4=168.980;
        L=-24.280;
        tool_offset = new double[]{10,0,1};
        NOSOLUTION = 1000;
        v_max=50;
        theta_speed_max = new double[]{50.0,50.0,50.0,250.0/3.0,250.0/3.0,250.0/3.0};// deg/s
        theta_speed=new double[6];
        a_max_fast=new double[]{500,500,500,500,500,500};// deg/s^2
        a_max_forward=20;//mm/s
        a_fast=new double[6];
        w_fast=new double[6];
        v_forward=new double[3];
        a_forward=new double[3];
        v_doorlike=new double[3];
    }

    public double[][] MatrixMult(double[][] m1,double[][]m2){
        int i;
        int j;
        int k;

        int m=m1.length,r=m2.length,n=m2[0].length;
        double[][] out=new double[m][n];
        for (i = 0; i < m; i++) {
            for (j = 0; j < n; j++) {
                for (k = 0; k < r; k++) {
                    out[i][j]+=m1[i][k]*m2[k][j];
                }
            }
        }
        return out;
    }

    public double[][] transpose(double[][] a){
        if(a.length==0) return a;
        int m=a.length,n=a[0].length;
        double[][] ret=new double[n][m];
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < m; j++) {
                ret[i][j] = a[j][i];
            }
        }
        return ret;
    }

    public double[] F_inverse(double[] X_tar,double[]R_tar,double[]THETA_0){
        double A2xA2_		= A2 * A2;
        double A3xA3_		= A3 * A3;
        double D4xD4_		= D4 * D4;
        double D4_A3		= Math.sqrt(D4xD4_ + A3xA3_);
        double ATAN2D4_A3	= Math.atan2(D4, A3);
        double[] THETA_target=new double[6];

        double alpha=R_tar[0]*PI/180;
        double beta=R_tar[1]*PI/180;
        double gama=R_tar[2]*PI/180;

        double  temp1 = Math.cos(alpha);//三角函数用弧度制
        double  temp2 = Math.cos(beta);
        double  temp3 = Math.cos(gama);
        double  temp4 = Math.sin(alpha);
        double  temp5 = Math.sin(beta);
        double  temp6 = Math.sin(gama);

        double[][] R60 = new double[][]{
                { temp2*temp3 , temp3*temp4*temp5 - temp1*temp6 , temp1*temp3*temp5 + temp4*temp6},
                { temp2*temp6 , temp4*temp5*temp6 + temp1*temp3 , temp1*temp5*temp6 - temp3*temp4},
                {-temp5       , temp2*temp4                     , temp1*temp2                    }
        };

        double[][] T_tool_0 = new double[][]{
                { temp2*temp3 , temp3*temp4*temp5 - temp1*temp6 , temp1*temp3*temp5 + temp4*temp6 , X_tar[0]},
                { temp2*temp6 , temp4*temp5*temp6 + temp1*temp3 , temp1*temp5*temp6 - temp3*temp4 , X_tar[1]},
                {-temp5       , temp2*temp4                     , temp1*temp2                     , X_tar[2]},
                {            0,                                0,                                0,       1}
        };

        double[][] inv_Ttool_6 = new double[][]{
                {    1,   0 ,   0,  -tool_offset[0]},
                {    0,   1 ,   0,  -tool_offset[1]},
                {    0,   0 ,   1,   tool_offset[2]},
                {    0,   0 ,   0,  1}
        };

        double[][] T60=MatrixMult(T_tool_0,inv_Ttool_6);

        double xtip = T60[0][3] + R60[0][2] * Math.abs(L);
        double ytip = T60[1][3] + R60[1][2] * Math.abs(L);
        double ztip = T60[2][3] + R60[2][2] * Math.abs(L);

        // compute theta1
        double theta1  = Math.atan2(ytip,xtip);

        // compute theta33
        double s = ztip - D1;
        double r = Math.sqrt(Math.pow(xtip - A1*Math.cos(theta1), 2) + Math.pow((ytip - A1*Math.sin(theta1)), 2));
        double czeta = (r*r + s*s  - A2xA2_ - D4xD4_ - A3xA3_) / (2 * A2 * D4_A3);
        double zeta1, theta33;
        if (Math.abs(czeta) <= 1){
            double szeta = Math.sqrt(1 - czeta*czeta);
            zeta1  = -Math.atan2(szeta,czeta);
            theta33 = -(zeta1 + ATAN2D4_A3);
        } else {
            theta33 = NOSOLUTION;
            //System.out.print("error: theta33 has no solution!\n");
            for(int i=0;i<6;i++){THETA_target[i]=NOSOLUTION;}
            return THETA_target;
        }
        // compute theta2i
        double theta2i = Math.atan2(D4_A3 * Math.sin(zeta1), A2 + D4_A3 * Math.cos(zeta1)) - Math.atan2(s, r);
        // compute theta 456/445566
        temp1 = Math.cos(theta1);
        temp2 = Math.sin(theta1);
        temp3 = Math.cos(theta2i+theta33);
        temp4 = Math.sin(theta2i+theta33);

        double[][] R30=new double[][]{
                { temp1 * temp3 , -temp1 * temp4 , -temp2},      // 这个使用T矩阵计算出来的，注意三角函数做了合并
                { temp2 * temp3 , -temp2 * temp4 , temp1},      // 这里选择了上边cita123的SOL3这组解
                {-temp4         , -temp3         , 0    }
        };
        double[][] RT63_cita456 = {{1,0,0},
                {0,0,1},
                {0,-1,0}}; // RT63: R63 transpose，R63: when cita456 = 0/0/0
        double[][] R63 =MatrixMult((MatrixMult(RT63_cita456,transpose(R30))),R60);
        double theta5 = Math.atan2(Math.sqrt(Math.pow(R63[2][0],2) + Math.pow(R63[2][1],2)), R63[2][2]);

        double theta4, theta6;
        if (Math.abs(theta5) < 0.0001) {
            theta4 = 0;
            theta5 = 0;
            theta6 =  Math.atan2(-R63[0][1], R63[0][0]);
        } else if (Math.abs(theta5-PI) < 0.0001) {
            theta4 = 0;
            theta5 = PI;
            theta6 =  Math.atan2(R63[0][1],-R63[0][0]);
        } else {
            temp1 = Math.sin(theta5);
            theta4 = -Math.atan2 (R63[1][2]/ temp1, R63[0][2]/ temp1);
            theta6 = Math.atan2((R63[2][1]/ temp1), (-R63[2][0]/ temp1));

            double theta55 = -theta5;
            double theta44 =  -Math.atan2 (R63[1][2]/ theta55, R63[0][2]/ theta55);
            double theta66 =  Math.atan2((R63[2][1]/ theta55), (- R63[2][0]/ theta55));
            // select from theta456 and theta445566
            double sum_a = Math.abs(THETA_0[3] - theta4*180/PI) + Math.abs(THETA_0[4] - (theta5*180/PI - 90)) + Math.abs(THETA_0[5] - theta6*180/PI);
            double sum_b = Math.abs(THETA_0[3] - theta44*180/PI) + Math.abs(THETA_0[4] - (theta55*180/PI - 90)) + Math.abs(THETA_0[5] - theta66*180/PI);
            if (sum_a > sum_b) {
                theta4 = theta44;
                theta5 = theta55;
                theta6 = theta66;
            }
        }

        THETA_target[0] = theta1*180/PI;
        THETA_target[1] = theta2i*180/PI + 90;
        THETA_target[2] = theta33*180/PI;
        THETA_target[3] = theta4*180/PI;
        THETA_target[4] = theta5*180/PI - 90;
        THETA_target[5] = theta6*180/PI;

        return  THETA_target;
    }
    public double[] F_forward(double[] THETA){
        double[] tool = new double[3];

        THETA[1]=THETA[1]-90;
        THETA[4]=THETA[4]+90;

        double[] sinTemp=new double[6];
        double[] cosTemp=new double[6];

        for(int i=0;i<6;i++){
            THETA[i]=Math.toRadians(THETA[i]);
            sinTemp[i]=Math.sin(THETA[i]);
            cosTemp[i]=Math.cos(THETA[i]);
        }

        double[][]T10= new double[][]{
                {cosTemp[0],  -sinTemp[0],  0,  0},
                {sinTemp[0],   cosTemp[0],  0,  0},
                {0,            0,           1,  D1},
                {0,            0,           0,  1}
        };
        double[][]T21= new double[][]{
                {cosTemp[1],  -sinTemp[1],  0,  A1},
                {0,           0,            1,  0},
                {-sinTemp[1], -cosTemp[1],  0,  0},
                {0,            0,           0,  1}
        };
        double[][]T32= new double[][]{
                {cosTemp[2],  -sinTemp[2],  0,  A2},
                {sinTemp[2],   cosTemp[2],  0,  0},
                {0,            0,           1,  0},
                {0,            0,           0,  1}
        };
        double[][]T43= new double[][]{
                {cosTemp[3],  -sinTemp[3],  0,  A3},
                {0,           0,            1,  D4},
                {-sinTemp[3], -cosTemp[3],  0,  0},
                {0,            0,           0,  1}
        };
        double[][]T54= new double[][]{
                {cosTemp[4],  -sinTemp[4],  0,  0},
                {0,           0,            -1, 0},
                {sinTemp[4], cosTemp[4],    0,  0},
                {0,            0,           0,  1}
        };
        double[][]T65= new double[][]{
                {cosTemp[5],  -sinTemp[5],  0,  0},
                {0,           0,            -1, -L},
                {sinTemp[5], cosTemp[5],    0,  0},
                {0,            0,           0,  1}
        };
        double[][]Ttool_6= new double[][]{
                {1,  0,  0,  tool_offset[0]},
                {0,  1,  0,  tool_offset[1]},
                {0,  0,  1,  tool_offset[2]},
                {0,  0,  0,  1}
        };
        double[][]Ttool_0=MatrixMult(MatrixMult(MatrixMult(MatrixMult(MatrixMult(MatrixMult(T10,T21),T32),T43),T54),T65),Ttool_6);

        if(Math.abs(Ttool_0[0][0])<0.001) Ttool_0[0][0]=0;
        if(Math.abs(Ttool_0[1][0])<0.001) Ttool_0[1][0]=0;
        if(Math.abs(Ttool_0[2][0])<0.001) Ttool_0[2][0]=0;
        if(Math.abs(Ttool_0[2][1])<0.001) Ttool_0[2][1]=0;
        if(Math.abs(Ttool_0[2][2])<0.001) Ttool_0[2][2]=0;

        //double temp=Math.sqrt(Math.pow(Ttool_0[2][1],2)+Math.pow(Ttool_0[2][2],2));
        double[] X=new double[3];
        X[0]=Ttool_0[0][3];
        X[1]=Ttool_0[1][3];
        X[2]=Ttool_0[2][3];

        return X;
    }

    public double[] Solve_omega_bar(double[] theta_0,double[] theta_target){
        double[] omega_bar=new double[6];
        double t_max = 0.0;
        for(int i=0;i<6;i++){
            t_max=Math.max((theta_target[i]-theta_0[i])/theta_speed_max[i],t_max);
        }
        for(int i=0;i<6;i++){
            omega_bar[i]=(theta_target[i]-theta_0[i])/t_max;
        }
        return omega_bar;
    }

    public double[] Solve_T12_zero(double[] delta_theta){
        double[] time=new double[]{0.1};

        for(int i=0;i<6;i++){
            theta_speed[i]= delta_theta[i];
        }
        return time;
    }

    public double[] Solve_T12(double[] delta_theta){
        double[] time=new double[3];
        double maxt1=0,maxt2=0;
        for(int i=0;i<6;i++){
            double delta=Math.abs(delta_theta[i]);
            double t1=theta_speed_max[i]/a_max_fast[i];
            double t2=delta/theta_speed_max[i]-t1;
            if(t2<0){
                t2=0;
                t1=Math.sqrt(delta/a_max_fast[i]);
            }
            double totaltime=2*t1+t2;
            if(2*maxt1+maxt2<totaltime){
                maxt1=t1;
                maxt2=t2;
            }
        }
        for(int i=0;i<6;i++){
            a_fast[i]=delta_theta[i]/(maxt1*maxt1+maxt1*maxt2);
            w_fast[i]=a_fast[i]*maxt1;
        }

        time[0]=maxt1;
        time[1]=maxt1+maxt2;
        time[2]=2*maxt1+maxt2;
        return time;
    }
    public double[] Solve_T12_forward(double[] delta_X,double V_tar){
        double[] time = new double[3];
        double sum=Math.abs(delta_X[0])+Math.abs(delta_X[1])+Math.abs(delta_X[2]);
        int max_index=0;
        for(int i=0;i<3;i++){
            v_forward[i]=(delta_X[i]/sum)*V_tar;
            if(Math.abs(delta_X[max_index])<Math.abs(delta_X[i])) max_index=i;
        }

        if(delta_X[max_index]<0) a_forward[max_index]=-20;
        else a_forward[max_index]=20;
        for(int i=0;i<3;i++){
            a_forward[i]=delta_X[i]/Math.abs(delta_X[max_index])*20;
        }
        double t0=Math.abs(v_forward[0]/a_forward[0]);
        double t1=Math.abs(delta_X[0]/v_forward[0]-time[0]);
        time[0]=t0;
        time[1]=time[0]+t1;
        time[2]=time[1]+time[0];

        for(int i=0;i<3;i++){
            if(Math.abs((t0+t1)*v_forward[i])>Math.abs(delta_X[i])){
                v_forward[i]=delta_X[i]/(t0+t1);
                a_forward[i]=v_forward[i]/t0;
            }
        }
        return time;
    }

    public double[] Solve_T12_doorlike(double[] delta_x, double height) {
        double t1=height/v_max;
        double t2=Math.max(Math.abs(delta_x[0]),Math.max(Math.abs(delta_x[1]),Math.abs(delta_x[2])))/v_max;
        for(int i=0;i<3;i++){
            v_doorlike[i]=delta_x[i]/t2;
        }
        double t3=height/v_max;
        return new double[]{t1,t1+t2,t1+t2+t3};
    }
}
