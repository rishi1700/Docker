function RedirectToConsole(imageName,portNo,directUrl)
{
    var port = (portNo != null) ? portNo : '80';
    
    var currentLocation = window.location.hostname;
    
    var url="http://"+currentLocation+":"+port;
    //console.log(url)

    var defaultImages = [
        'simple-web','minio','redmine','suitecrm','cassandra','datadoghq-agent','fedena','opensis', 
        'moodle', 'sanuyi-dvr', 'onlyoffice', 'lets-chat', 'orangehrm', 'grafana', 'wordpress',
        'kibana', 'xibo', 'erpnext', 'mahara','openproject','logicaldoc','canvas','tastyigniter',
        'openemr','frontaccounting','akaunting','yetiforce','cliniccases','screenly','alluxio','syncthing',
        'jupyter','ospos','nextcloud','open-xchange','jitsi',"ubuntu-os", "ubuntu-os-ssh","jellyfin","portainer",
		"elasticsearch","solr","opensis:9.1","ubuntu-gotty:1.0","mysql:8.0"
    ]
    if(defaultImages.includes(imageName))
	{				
        url = url
    }
    else if(imageName=='kdenlive' || imageName=='kdenlive:1.0' || imageName=='sanuyirepo/kdenlive:1.0') {
        if (portNo == null) {
            port = '3001';
        }
        url = "https://" + currentLocation + ":" + port;
    }
    else if(imageName=='odoo') {
        url = url + "/web/database/manager";
    }
    else if(imageName=='openemis') {
        url = url + "/core/";
    }
    else if(imageName=='ofbiz') {
        url="https://"+currentLocation+":"+port;
        url = url + "/webtools/";
    }
    else if(imageName=='isard') {
        url="https://"+currentLocation+":"+port;
    }
    else if(imageName=='p5-server' || imageName == 'sanuyi-archiver 1.0.3' || imageName == 'archiware:7.4.5' || imageName == "sanuyi-archiver:1.0.3") {
        url=url + "/login"
    }

    if(directUrl){
            window.open(url);
    }
    else{
        window.location.href = url;
    }
        
}
